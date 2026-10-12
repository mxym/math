import ContinuumGeometric
open ContinuumGeometric
example : (4 : ℤ) ∈ activeIntegers 8 16 2 := by
  rw [mem_activeIntegers_iff 8 16 2 (by norm_num)]
  norm_num
