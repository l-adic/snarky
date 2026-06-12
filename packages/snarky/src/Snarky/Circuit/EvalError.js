// Tagged-exception transport for EvaluationError. The symbol is private to
// this module, so only values thrown by `throwEvalErrorImpl` are recovered
// by `catchEvalErrorImpl`; everything else rethrows.
const TAG = Symbol("snarky.EvaluationError");

export const throwEvalErrorImpl = (e) => () => {
  const err = new Error("snarky EvaluationError (uncaught — should have been recovered at an interpreter boundary)");
  err[TAG] = e;
  throw err;
};

export const catchEvalErrorImpl = (left) => (right) => (eff) => () => {
  try {
    return right(eff());
  } catch (err) {
    if (err != null && err[TAG] !== undefined) return left(err[TAG]);
    throw err;
  }
};
