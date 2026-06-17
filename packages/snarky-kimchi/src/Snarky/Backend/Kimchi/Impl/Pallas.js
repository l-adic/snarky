// kimchi-napi-backed Snarky backend for Pallas-committed circuits
// (PallasScalarField = Fq).
//
// In our project naming this file serves the WRAP circuit family:
//   * scalar field = Fq        (Pallas.ScalarField)
//   * curve coords = Fp        (Pallas.BaseField = Vesta.ScalarField)
//   * commitments live on Pallas.G
//
// kimchi-napi's "Fq" half maps to this same world:
//   * `caml_pasta_fq_plonk_*`  — Fq circuits, Pallas commitments
//   * `caml_fq_srs_*`          — SRS over Pallas (group whose scalar = Fq)
//   * `WasmPastaFqPlonkIndex`  — ProverIndex<Pallas>
//   * `WasmFqSrs`              — Pallas SRS
//
// Field-element wire encoding: kimchi-napi serializes `NapiPastaFq` via
// `CanonicalSerialize` (Arkworks `serialize_compressed`) = 32 LE bytes.
// We feed JS bigints in by encoding via `Fq.toBytesLE`; we decode return
// values via `Fq.fromBytesLE`. The same applies to `Fp` for curve coords.

import { createRequire } from 'module';
import { Fp, Fq } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// ---------------------------------------------------------------------------
// Codec helpers — bigint <-> 32-byte LE buffer / array
// ---------------------------------------------------------------------------

// Curve coords (Pallas points live in Fp). Decodes the 32-byte LE buffer
// kimchi-napi hands back for a point coordinate.
function fpFromBytes(bufLike) {
    return Fp.fromBytesLE(bufLike instanceof Uint8Array ? bufLike : new Uint8Array(bufLike));
}

// FlatVector<NapiPastaFq> wire layout: a single Uint8Array of n*32 bytes.
function fqFlatVector(arr) {
    const out = new Uint8Array(arr.length * 32);
    for (let i = 0; i < arr.length; i++) {
        out.set(Fq.toBytesLE(arr[i]), i * 32);
    }
    return out;
}

// ---------------------------------------------------------------------------
// GateKind <-> kimchi-napi `gate_type_from_i32` discriminant
// ---------------------------------------------------------------------------

// Matches the `variants` table at gate_vector.rs:265-284:
//   Zero=0, Generic=1, Poseidon=2, CompleteAdd=3, VarBaseMul=4,
//   EndoMul=5, EndoMulScalar=6, ...
// Our PS-side GateKind names (from Snarky.Constraint.Kimchi.Types.gateKindToString):
const KIND_TO_TYP = Object.freeze({
    Zero: 0,
    GenericPlonkGate: 1,
    PoseidonGate: 2,
    AddCompleteGate: 3,
    VarBaseMul: 4,
    EndoMul: 5,
    EndoScalar: 6, // kimchi-napi calls this `EndoMulScalar`
});

function gateKindToTyp(name) {
    const t = KIND_TO_TYP[name];
    if (t === undefined) throw new Error(`pallasCircuitGateNew: unknown gate kind '${name}'`);
    return t;
}

// ---------------------------------------------------------------------------
// Gates
// ---------------------------------------------------------------------------

// `gate` is the kimchi-napi `NapiFqGate` object literal:
//   { typ: i32, wires: NapiGateWires, coeffs: number[] (flat LE bytes) }
export function pallasCircuitGateNew(gateKind) {
    return function(wires) {
        return function(coeffs) {
            const coeffBytes = new Array(coeffs.length * 32);
            for (let i = 0; i < coeffs.length; i++) {
                const b = Fq.toBytesLE(coeffs[i]);
                for (let j = 0; j < 32; j++) coeffBytes[i * 32 + j] = b[j];
            }
            return {
                typ: gateKindToTyp(gateKind),
                wires,
                coeffs: coeffBytes,
            };
        };
    };
}

export function pallasCircuitGateGetWires(gate) {
    return gate.wires;
}

export function pallasCircuitGateCoeffCount(gate) {
    return (gate.coeffs.length / 32) | 0;
}

export function pallasCircuitGateGetCoeff(gate) {
    return function(index) {
        const off = index * 32;
        const slice = new Uint8Array(32);
        for (let j = 0; j < 32; j++) slice[j] = gate.coeffs[off + j];
        return Fq.fromBytesLE(slice);
    };
}

// ---------------------------------------------------------------------------
// SRS
// ---------------------------------------------------------------------------
//
// kimchi-napi has no single `size` accessor on `WasmFqSrs`, so we wrap
// the underlying SRS together with its depth at construction time. PS
// holds this as the opaque `CRS Pallas.G` type.

const SRS_DEFAULT_DEPTH = 1 << 16;

export function pallasCrsLoadFromCache() {
    // No cached path here yet — proof-cache + SRS regeneration is a later
    // slice. Fall back to constructing a fresh SRS of the default depth.
    const srs = k.caml_fq_srs_create(SRS_DEFAULT_DEPTH);
    return { srs, size: SRS_DEFAULT_DEPTH };
}

export function pallasCrsCreate(depth) {
    const srs = k.caml_fq_srs_create(depth);
    return { srs, size: depth };
}

export function pallasCrsSize(crs) {
    return crs.size;
}

// Pre-warm the lagrange-basis cache for the domain of size `2^log2Size`.
// The cache lives inside the shared SRS object (interior mutability), so
// later `index_create` / `proof_create` over that domain hit the cache
// instead of recomputing the basis. Effectful: mutates the SRS in place.
export function pallasSrsAddLagrangeBasis(crs) {
    return function(log2Size) {
        return function() {
            k.caml_fq_srs_add_lagrange_basis(crs.srs, log2Size);
        };
    };
}

// Serialize the lagrange basis for domain 2^log2Size. napi returns a Uint8Array
// (portable across the napi + wasm builds); we pass it through untouched.
export function pallasSrsLagrangeBasisToBytes(crs) {
    return function(log2Size) {
        return function() {
            return k.caml_fq_srs_lagrange_basis_to_bytes(crs.srs, log2Size);
        };
    };
}

// Inject a serialized lagrange basis into the SRS cache for domain 2^log2Size.
export function pallasSrsSetLagrangeBasisFromBytes(crs) {
    return function(log2Size) {
        return function(bytes) {
            return function() {
                k.caml_fq_srs_set_lagrange_basis_from_bytes(crs.srs, log2Size, bytes);
            };
        };
    };
}

// Serialize the SRS generators (g, h) — the basis cache is serde-skipped.
export function pallasSrsToBytes(crs) {
    return function() {
        return k.caml_fq_srs_to_bytes(crs.srs);
    };
}

// Reconstruct an SRS (generators only) from bytes, tagged with `size`.
export function pallasSrsFromBytes(size) {
    return function(bytes) {
        return function() {
            return { srs: k.caml_fq_srs_from_bytes(bytes), size };
        };
    };
}

// b_poly commitment: takes Pallas scalars (Fq), returns a `PolyComm<Pallas>`
// whose points have Fp coords. PS-side currently expects a flat
// `Array Pallas.BaseField` of length 2 (x, y); we expose the first
// `unshifted` chunk in that flat shape for API compatibility.
export function pallasSrsBPolyCommitment(crs) {
    return function(challenges) {
        const pc = k.caml_fq_srs_b_poly_commitment(crs.srs, fqFlatVector(challenges));
        const first = pc.unshifted[0];
        return [fpFromBytes(first.x), fpFromBytes(first.y)];
    };
}

// ---------------------------------------------------------------------------
// Circuit serialization — debug JSON dump of the gate sequence
// ---------------------------------------------------------------------------

export function pallasGatesToJson(gates) {
    return function(publicInputSize) {
        const gv = k.caml_pasta_fq_plonk_gate_vector_create();
        for (const g of gates) {
            k.caml_pasta_fq_plonk_gate_vector_add(gv, g);
        }
        return k.caml_pasta_fq_plonk_circuit_serialize(publicInputSize, gv);
    };
}

// ---------------------------------------------------------------------------
// Prover / verifier index
// ---------------------------------------------------------------------------

// `caml_pasta_fq_plonk_index_create(gates, public_, lookup_tables,
//  runtime_table_cfgs, prev_challenges, srs, lazy_mode)` returns an
// `External<WasmPastaFqPlonkIndex>` which PS treats as the opaque
// `ProverIndex Pallas.G PallasScalarField`.
//
// Pickles never uses kimchi's lookup feature, so `lookup_tables` and
// `runtime_table_cfgs` are always empty. `lazy_mode = false` matches OCaml's
// default.
export function pallasProverIndexCreate({
    gates,
    publicInputSize,
    prevChallengesCount,
    maxPolySize,
    crs,
}) {
    void maxPolySize; // kimchi-napi derives chunking from srs + domain automatically
    const gv = k.caml_pasta_fq_plonk_gate_vector_create();
    for (const g of gates) {
        k.caml_pasta_fq_plonk_gate_vector_add(gv, g);
    }
    return k.caml_pasta_fq_plonk_index_create(
        gv,
        publicInputSize,
        [],                 // lookup_tables
        [],                 // runtime_table_cfgs
        prevChallengesCount,
        crs.srs,
        false,              // lazy_mode
    );
}

// `caml_pasta_fq_plonk_verifier_index_create(index)` produces a
// `NapiPlonkVerifierIndex` (a plain serializable object). PS holds it as
// the opaque `VerifierIndex Pallas.G PallasScalarField` type.
export const vestaVerifierIndex = (proverIndex) =>
    k.caml_pasta_fq_plonk_verifier_index_create(proverIndex);
