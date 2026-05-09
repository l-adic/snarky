import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const pallasSrsBlindingGenerator = (srs) => {
  const flat = crypto.pallasSrsBlindingGenerator(srs);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsBlindingGenerator = (srs) => {
  const flat = crypto.vestaSrsBlindingGenerator(srs);
  return { x: flat[0], y: flat[1] };
};

export const pallasSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.pallasSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsLagrangeCommitmentAt = (srs) => (domainLog2) => (i) => {
  const flat = crypto.vestaSrsLagrangeCommitmentAt(srs, domainLog2, i);
  return { x: flat[0], y: flat[1] };
};
