// Typed accessors over a Transport JS object
// { myId, broadcast(msg), sendTo(peer,msg), onMessage(fn), onPeer(fn) }.
export const _myId = (t) => t.myId;
export const _broadcast = (t, msg) => t.broadcast(msg);
export const _sendTo = (t, { peer, msg }) => t.sendTo(peer, msg);
export const _onMessage = (t, fn) => t.onMessage((from, raw) => fn(from, raw));
export const _onPeer = (t, fn) => t.onPeer((peer) => fn(peer));
export const _onPeerLeave = (t, fn) => t.onPeerLeave((peer) => fn(peer));

// Adapt a curried PS handler `a -> b -> Effect Unit` into an EffectFn2.
export const mkHandler2 = (f) => (a, b) => f(a)(b)();
export const mkHandler1 = (f) => (a) => f(a)();

// Build the `{ myId, broadcast, sendTo, onMessage, onPeer }` object the accessors
// above expect from a PureScript `TransportImpl`, whose fields are curried Effect
// functions (`broadcast :: msg -> () -> unit`, etc.). Force the Effect thunks and
// re-curry the registered handlers (the accessors call them as `(from, raw)`).
export const fromImpl = (impl) => ({
  myId: impl.myId,
  broadcast: (msg) => impl.broadcast(msg)(),
  sendTo: (peer, msg) => impl.sendTo(peer)(msg)(),
  onMessage: (fn) => impl.onMessage((from) => (raw) => () => fn(from, raw))(),
  onPeer: (fn) => impl.onPeer((id) => () => fn(id))(),
  onPeerLeave: (fn) => impl.onPeerLeave((id) => () => fn(id))(),
});
