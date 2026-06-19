// self.postMessage of a pre-encoded wire object (a WorkerMsg). Shared by the
// worker entry (Worker.purs) and its logger (WorkerLog.purs); in either worker
// `self` is the worker and the host receives the message.
export const post = (value) => () => {
  self.postMessage(value);
};
