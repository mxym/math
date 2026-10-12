import ContinuumRemainder.FinalProof
open Set ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
example : ((⟨1, by norm_num⟩,⟨1,by norm_num⟩) : PowerParams 1 2) ∈ logActivation 1 0 1 2 := by
  norm_num [logActivation]
