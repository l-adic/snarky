// Worker-side prover-service log hook. The worker installs
// globalThis.__svcLog to forward structured {severity, text} lines to the page.
export const svcLog = (obj) => () => {
  if (globalThis.__svcLog) globalThis.__svcLog(obj);
};
