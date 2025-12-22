import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const crypto = require('snarky-crypto');

export const verifyPallasPoseidon = ({ row, nextRow, coeffs }) => crypto.verifyPallasPoseidon(row, nextRow, coeffs);

export const verifyVestaPoseidon = ({ row, nextRow, coeffs }) => crypto.verifyVestaPoseidon(row, nextRow, coeffs);