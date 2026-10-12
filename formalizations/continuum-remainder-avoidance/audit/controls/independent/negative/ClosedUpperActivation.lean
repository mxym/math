import ContinuumRemainder.LogGeometry
open ContinuumRemainder ContinuumGeometric
example : ((⟨2, by norm_num⟩, ⟨2, by norm_num⟩) : PowerParams 1 2) ∈
    logActivation 2 1 1 3 := by norm_num [logActivation]
