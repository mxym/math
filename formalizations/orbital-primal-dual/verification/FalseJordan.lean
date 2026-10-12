import ProofBundle

open scoped BigOperators

-- Expected rejection.  The supplied vector has nonzero total signed mass.
-- The positive control proves that its proposed Jordan law has total mass two.
theorem invalid_jordan_normalization :
    OrbitalMarginals.Probability
      (OrbitalMarginals.jordanP (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 0)) := by
  constructor
  · intro i
    exact div_nonneg (le_max_right _ _) (OrbitalMarginals.tv_nonneg _)
  · rw [OrbitalMarginals.jordan_requires_zero_mass.2]
    norm_num
