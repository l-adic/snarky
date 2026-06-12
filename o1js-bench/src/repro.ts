// Minimal repro for the b0 'Constraint unsatisfied (Checked.inv /
// scalars_env / prevs_verified)' failure seen on the native backend:
// same program shape as programs.ts but with no filler, so compile is
// fast. Run with O1JS_BACKEND=wasm and =native to bisect program bug
// vs backend bug.
import { setBackend } from 'o1js';

const BACKEND = (process.env.O1JS_BACKEND ?? 'wasm') as 'wasm' | 'native';
if (BACKEND === 'native') setBackend('native');
console.log(`[backend] ${BACKEND}`);

const { Field, Provable, SelfProof, ZkProgram, verify } = await import('o1js');
type SelfProofT = InstanceType<typeof SelfProof<undefined, InstanceType<typeof Field>>>;

const Nrr = ZkProgram({
  name: 'repro-nrr',
  publicOutput: Field,
  methods: {
    base: {
      privateInputs: [],
      async method() {
        return { publicOutput: Field(0) };
      },
    },
  },
});
class NrrProof extends ZkProgram.Proof(Nrr) {}

const Tree = ZkProgram({
  name: 'repro-tree',
  publicOutput: Field,
  methods: {
    step: {
      privateInputs: [NrrProof, SelfProof],
      async method(nrrProof: NrrProof, selfProof: SelfProofT) {
        nrrProof.verify();
        const prevOut = selfProof.publicOutput;
        const isBaseCase = prevOut.equals(Field(-1));
        selfProof.verifyIf(isBaseCase.not());
        const out = Provable.if(isBaseCase, Field(0), prevOut.add(1));
        return { publicOutput: out };
      },
    },
  },
});
class TreeProof extends ZkProgram.Proof(Tree) {}

console.log('compiling Nrr ...');
await Nrr.compile();
console.log('compiling Tree ...');
const { verificationKey } = await Tree.compile();

console.log('proving nrr.base ...');
const nrrProof = (await Nrr.base()).proof;
console.log('making dummy self proof ...');
const domainLog2 = process.env.DUMMY_DOMAIN_LOG2 ? Number(process.env.DUMMY_DOMAIN_LOG2) : undefined;
console.log('dummy domainLog2 =', domainLog2 ?? 'default(14)');
const dummy = (await TreeProof.dummy(undefined, Field(-1), 2, domainLog2)) as unknown as SelfProofT;

console.log('proving tree.step b0 (base case, dummy self) ...');
const b0 = (await Tree.step(nrrProof, dummy)).proof;
console.log('b0 ok, publicOutput =', b0.publicOutput.toString());

console.log('proving tree.step b1 (merge over b0) ...');
const b1 = (await Tree.step(nrrProof, b0)).proof;
console.log('b1 ok, publicOutput =', b1.publicOutput.toString());

const ok = await verify(b1, verificationKey);
console.log('verify(b1) =', ok);
process.exit(ok ? 0 : 1);
