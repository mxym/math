import ContinuumGeometric
open ContinuumGeometric
example : (9 : ℕ) ∈ activeNaturals 10 16 1 := by
  rw [mem_activeNaturals_iff 10 16 1 (by norm_num) (by norm_num)]
  norm_num
