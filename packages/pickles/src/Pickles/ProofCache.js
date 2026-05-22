// FFI for Pickles.ProofCache's VK json-key.
//
// VerifierIndex JSON-key decompose — peel a kimchi napi `VerifierIndex`
// into a typed PS-side record (`VkRaw` in `Pickles.ProofCache.purs`). PS
// owns the structural assembly + Argonaut JSON-stringification; this JS
// side does exactly two irreducible bits:
//   (1) reach into the napi object's snake_case fields, and
//   (2) hex-encode the 32-byte `NapiPasta*` buffers.
//
// All policy about WHICH fields enter the key, optionality handling, and
// JSON-shape lives in PS (only `vestaVerifierIndexJsonKey` is exported
// from the PS module; the `VkRaw`/helper types are module-private).

function bytesHex(buf) {
  const b = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
  let s = "";
  for (let i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, "0");
  return s;
}

const _affine = (p) => ({ x: bytesHex(p.x), y: bytesHex(p.y) });
const _polyComm = (pc) => ({ unshifted: pc.unshifted.map(_affine) });
const _optPolyComm = (pc) => (pc == null ? null : _polyComm(pc));

export function _vkRaw(vi) {
  const ev = vi.evals;
  return {
    domain: {
      logSizeOfGroup: vi.domain.log_size_of_group,
      groupGen: bytesHex(vi.domain.group_gen),
    },
    maxPolySize: vi.max_poly_size,
    publicInputs: vi.public_,
    prevChallenges: vi.prev_challenges,
    zkRows: vi.zk_rows,
    shifts: [vi.shifts.s0, vi.shifts.s1, vi.shifts.s2, vi.shifts.s3, vi.shifts.s4, vi.shifts.s5, vi.shifts.s6].map(bytesHex),
    evals: {
      sigmaComm: ev.sigma_comm.map(_polyComm),
      coefficientsComm: ev.coefficients_comm.map(_polyComm),
      genericComm: _polyComm(ev.generic_comm),
      psmComm: _polyComm(ev.psm_comm),
      completeAddComm: _polyComm(ev.complete_add_comm),
      mulComm: _polyComm(ev.mul_comm),
      emulComm: _polyComm(ev.emul_comm),
      endomulScalarComm: _polyComm(ev.endomul_scalar_comm),
      xorComm: _optPolyComm(ev.xor_comm),
      rangeCheck0Comm: _optPolyComm(ev.range_check0_comm),
      rangeCheck1Comm: _optPolyComm(ev.range_check1_comm),
      foreignFieldAddComm: _optPolyComm(ev.foreign_field_add_comm),
      foreignFieldMulComm: _optPolyComm(ev.foreign_field_mul_comm),
      rotComm: _optPolyComm(ev.rot_comm),
    },
  };
}
