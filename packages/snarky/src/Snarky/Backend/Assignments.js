// Dense mutable assignment store, indexed by Variable's Int.
// Writes go through Effect (see Assignments.purs); reads are pure on the
// grounds that slots are write-once: a successful lookup is stable forever.

export const fresh = () => [];

// Frozen empty store: the safe value for `emptyProverState`'s field. The
// solver installs a fresh store per invocation; if a code path ever writes
// to the placeholder instead, strict mode throws instead of silently
// sharing state across solves.
export const emptyFrozen = Object.freeze([]);

export const setImpl = (i, v, store) => () => {
  store[i] = v;
};

export const lookupImpl = (just, nothing, i, store) => {
  const v = store[i];
  return v === undefined ? nothing : just(v);
};

export const foldEntriesImpl = (f, init, store) => {
  let acc = init;
  for (let i = 0; i < store.length; i++) {
    const v = store[i];
    if (v !== undefined) acc = f(acc)(i)(v);
  }
  return acc;
};
