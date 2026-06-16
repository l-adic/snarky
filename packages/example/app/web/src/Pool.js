// In a Web Worker, navigator.hardwareConcurrency reports the core count.
export const hardwareConcurrency = () => self.navigator?.hardwareConcurrency || 2;
