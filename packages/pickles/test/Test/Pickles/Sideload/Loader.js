// JSON parsing helpers for the side-load loader.
//
// `parseJsonPreserveBigInts` re-stringifies a JSON document with all
// integer values stored as strings, so that downstream argonaut decoding
// doesn't lose precision on int64 values that don't fit in JS Number's
// 53-bit mantissa. Used to decode OCaml `[@@deriving yojson]` output
// where 128-bit `Hex64` values are emitted as `[int64, int64]` pairs.

import JSONbigFactory from 'json-bigint';

const JSONbig = JSONbigFactory({ storeAsString: true });

export const parseJsonPreserveBigInts = (text) => {
    return JSON.stringify(JSONbig.parse(text));
};
