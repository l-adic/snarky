import PicklesFixture.CertificationDriver

/-!
Certify applications explicitly selected by APPS, from PICKLES_DUMP_DIR. Reconstruct each,
compile once and certify every step and wrap key against the Lean indices under the shared SRSs.
Report located failures and block their dependents. No foreign circuit dump or proof cache is read.
-/

def main : IO Unit := PicklesFixture.Application.runCertification true none
