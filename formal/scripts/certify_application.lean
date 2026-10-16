import PicklesFixture.CertificationDriver

/-!
Certify applications explicitly selected by APPS, from PICKLES_DUMP_DIR. Reconstruct each,
compile once and certify every step and wrap key against the Lean indices under the shared SRSs.
Compare the independent foreign circuit dumps with the certified Lean indices. Report located
failures and block their dependents. No proof cache is read.
-/

def main : IO Unit := PicklesFixture.Application.runCertification true none (compareDumps := true)
