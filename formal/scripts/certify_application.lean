import PicklesFixture.CertificationDriver

/-!
Certify applications explicitly selected by APPS, from PICKLES_DUMP_DIR. Reconstruct each,
compile once, compare its independently dumped indices and derive every step and wrap key
under the shared SRSs. Report located failures and block their dependents. No proof cache is read.
-/

def main : IO Unit := PicklesFixture.Application.runCertification true none
