import ContinuumGeometric

open ContinuumGeometric

-- Both endpoints are inactive: output logs 8 and 24 in the open window (8,24).
example : (4 : ℤ) ∉ activeIntegers 8 16 2 := by
  rw [mem_activeIntegers_iff 8 16 2 (by norm_num)]
  norm_num

example : (12 : ℤ) ∉ activeIntegers 8 16 2 := by
  rw [mem_activeIntegers_iff 8 16 2 (by norm_num)]
  norm_num

example : ((activeIntegers 8 16 2).card : ℝ) = 7 := by
  rw [activation_card_exact 8 16 2 (by norm_num) (by norm_num)]
  norm_num

example : ¬ (8 : ℝ) ≤ ((activeIntegers 8 16 2).card : ℝ) := by
  rw [activation_card_exact 8 16 2 (by norm_num) (by norm_num)]
  norm_num

-- The requested tail is expressed in original natural indices, not a sampled grid.
example : ∀ n ∈ activeNaturals 8 16 2, (4 : ℕ) ≤ n := by
  intro n hn
  have hmem := (mem_activeNaturals_iff 8 16 2 (by norm_num) (by norm_num) n).1 hn
  have : (4 : ℝ) < n := by linarith [hmem.1]
  exact_mod_cast this.le
