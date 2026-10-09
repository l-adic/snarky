import PicklesFixture.CertificationDriver

/-!
Derive every step and wrap verifier key from the reconstructed index and shared SRS. The default
manifest selection covers nonchunked self recursion (SimpleChainN2), self plus external recursion
(HeterogeneousPrevs, including its child), and chunked self recursion (SelfRecursiveChunks).
PICKLES_DUMP_DIR supplies the dump directory; APPS can override the selection. Every column,
chunk, metadata and the shape accumulator count is checked, and correspondence is retained in the
returned certificate. Report all entry failures and exit nonzero. No proof cache is read.
-/

def main : IO Unit := PicklesFixture.Application.runCertification false
  (some "SimpleChainN2,HeterogeneousPrevs,SelfRecursiveChunks")
