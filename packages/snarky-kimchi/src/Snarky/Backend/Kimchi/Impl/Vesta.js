// kimchi-napi-backed Snarky backend for Vesta-committed circuits
// (VestaScalarField = Fp). Mirror of `Impl/Pallas.js`; see that file's
// header for the full naming / field-layout explanation.
//
// In our project naming this file serves the STEP circuit family:
//   * scalar field = Fp        (Vesta.ScalarField)
//   * curve coords = Fq        (Vesta.BaseField = Pallas.ScalarField)
//   * commitments live on Vesta.G
//
// kimchi-napi's "Fp" half:
//   * `caml_pasta_fp_plonk_*`  — Fp circuits, Vesta commitments
//   * `caml_fp_srs_*`          — SRS over Vesta
//   * `WasmPastaFpPlonkIndex`  — ProverIndex<Vesta>
//   * `WasmFpSrs`              — Vesta SRS

import { createRequire } from 'module';
import { Fp, Fq } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

// ---------------------------------------------------------------------------
// Codec helpers
// ---------------------------------------------------------------------------

function fpFromBytes(bufLike) {
    return Fp.fromBytesLE(bufLike instanceof Uint8Array ? bufLike : new Uint8Array(bufLike));
}

function fqFromBytes(bufLike) {
    return Fq.fromBytesLE(bufLike instanceof Uint8Array ? bufLike : new Uint8Array(bufLike));
}

function fpFlatVector(arr) {
    const out = new Uint8Array(arr.length * 32);
    for (let i = 0; i < arr.length; i++) {
        out.set(Fp.toBytesLE(arr[i]), i * 32);
    }
    return out;
}

// ---------------------------------------------------------------------------
// GateKind discriminant — same table as Pallas
// ---------------------------------------------------------------------------

const KIND_TO_TYP = Object.freeze({
    Zero: 0,
    GenericPlonkGate: 1,
    PoseidonGate: 2,
    AddCompleteGate: 3,
    VarBaseMul: 4,
    EndoMul: 5,
    EndoScalar: 6,
});

function gateKindToTyp(name) {
    const t = KIND_TO_TYP[name];
    if (t === undefined) throw new Error(`vestaCircuitGateNew: unknown gate kind '${name}'`);
    return t;
}

// ---------------------------------------------------------------------------
// Gates — NapiFpGate shape: { typ, wires, coeffs: number[] flat LE bytes }
// ---------------------------------------------------------------------------

export function vestaCircuitGateNew(gateKind) {
    return function(wires) {
        return function(coeffs) {
            const coeffBytes = new Array(coeffs.length * 32);
            for (let i = 0; i < coeffs.length; i++) {
                const b = Fp.toBytesLE(coeffs[i]);
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

export function vestaCircuitGateGetWires(gate) {
    return gate.wires;
}

export function vestaCircuitGateCoeffCount(gate) {
    return (gate.coeffs.length / 32) | 0;
}

export function vestaCircuitGateGetCoeff(gate) {
    return function(index) {
        const off = index * 32;
        const slice = new Uint8Array(32);
        for (let j = 0; j < 32; j++) slice[j] = gate.coeffs[off + j];
        return Fp.fromBytesLE(slice);
    };
}

// ---------------------------------------------------------------------------
// SRS
// ---------------------------------------------------------------------------

const SRS_DEFAULT_DEPTH = 1 << 16;

export function vestaCrsLoadFromCache() {
    const srs = k.caml_fp_srs_create(SRS_DEFAULT_DEPTH);
    return { srs, size: SRS_DEFAULT_DEPTH };
}

export function vestaCrsCreate(depth) {
    const srs = k.caml_fp_srs_create(depth);
    return { srs, size: depth };
}

export function vestaCrsSize(crs) {
    return crs.size;
}

// Vesta b_poly commitment: inputs in Fp, outputs Vesta points (coords in Fq).
export function vestaSrsBPolyCommitment(crs) {
    return function(challenges) {
        const pc = k.caml_fp_srs_b_poly_commitment(crs.srs, fpFlatVector(challenges));
        const first = pc.unshifted[0];
        return [fqFromBytes(first.x), fqFromBytes(first.y)];
    };
}

// ---------------------------------------------------------------------------
// Circuit serialization
// ---------------------------------------------------------------------------

export function vestaGatesToJson(gates) {
    return function(publicInputSize) {
        const gv = k.caml_pasta_fp_plonk_gate_vector_create();
        for (const g of gates) {
            k.caml_pasta_fp_plonk_gate_vector_add(gv, g);
        }
        return k.caml_pasta_fp_plonk_circuit_serialize(publicInputSize, gv);
    };
}

// ---------------------------------------------------------------------------
// Prover / verifier index
// ---------------------------------------------------------------------------

export function vestaProverIndexCreate({
    gates,
    publicInputSize,
    prevChallengesCount,
    maxPolySize,
    crs,
}) {
    void maxPolySize;
    const gv = k.caml_pasta_fp_plonk_gate_vector_create();
    for (const g of gates) {
        k.caml_pasta_fp_plonk_gate_vector_add(gv, g);
    }
    return k.caml_pasta_fp_plonk_index_create(
        gv,
        publicInputSize,
        [],
        [],
        prevChallengesCount,
        crs.srs,
        false,
    );
}

export const pallasVerifierIndex = (proverIndex) =>
    k.caml_pasta_fp_plonk_verifier_index_create(proverIndex);

// Silence unused warning if not exercised.
void fpFromBytes;
