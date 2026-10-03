import { bigintsToBytes32LE } from 'pasta-runtime';

export const flatHexLe = (xs) => Buffer.from(bigintsToBytes32LE(xs)).toString('hex');
