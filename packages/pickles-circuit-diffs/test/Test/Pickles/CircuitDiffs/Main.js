import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const pallasSrsLagrangeCommitments = (srs) => (domainLog2) => (count) => {
  const flat = crypto.pallasSrsLagrangeCommitments(srs, domainLog2, count);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
};

export const pallasSrsBlindingGenerator = (srs) => {
  const flat = crypto.pallasSrsBlindingGenerator(srs);
  return { x: flat[0], y: flat[1] };
};

export const vestaSrsLagrangeCommitments = (srs) => (domainLog2) => (count) => {
  const flat = crypto.vestaSrsLagrangeCommitments(srs, domainLog2, count);
  const result = [];
  for (let i = 0; i < flat.length; i += 2) {
    result.push({ x: flat[i], y: flat[i + 1] });
  }
  return result;
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
