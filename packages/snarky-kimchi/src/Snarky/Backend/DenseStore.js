// Function-local mutable dense stores for constraint-system wiring.
export const freshImpl = () => [];
export const pushAtImpl = (i, v, s) => () => {
  const a = s[i];
  if (a === undefined) s[i] = [v];
  else a.push(v);
};
export const setAtImpl = (i, v, s) => () => { s[i] = v; };
export const getAtImpl = (just, nothing, i, s) => {
  const v = s[i];
  return v === undefined ? nothing : just(v);
};
export const foldSlotsImpl = (f, init, s) => {
  let acc = init;
  for (let i = 0; i < s.length; i++) {
    const v = s[i];
    if (v !== undefined) acc = f(acc)(i)(v);
  }
  return acc;
};

export const toEntriesImpl = (mk, s) => {
  const out = [];
  for (let i = 0; i < s.length; i++) {
    const v = s[i];
    if (v !== undefined) out.push(mk(i)(v));
  }
  return out;
};
