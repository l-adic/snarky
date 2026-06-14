// Typed accessors over a Transport JS object
// { myId, broadcast(msg), sendTo(peer,msg), onMessage(fn), onPeer(fn) }.
export const _myId = (t) => t.myId;
export const _broadcast = (t, msg) => t.broadcast(msg);
export const _sendTo = (t, { peer, msg }) => t.sendTo(peer, msg);
export const _onMessage = (t, fn) => t.onMessage((from, raw) => fn(from, raw));
export const _onPeer = (t, fn) => t.onPeer((peer) => fn(peer));

// Adapt a curried PS handler `a -> b -> Effect Unit` into an EffectFn2.
export const mkHandler2 = (f) => (a, b) => f(a)(b)();
export const mkHandler1 = (f) => (a) => f(a)();
