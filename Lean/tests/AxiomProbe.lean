import LandauerLaw
open UMST.LandauerLaw

/-!
  Negative regression: universal discharge via the old `physicalSecondLaw` axiom
  must not return. This file must **fail to elaborate** after P0-1.
-/

theorem axiom_probe_universal_discharge (proc : ErasureProcess) :
    physicalSecondLawUniformBinary proc :=
  physicalSecondLaw_uniform_binary proc
