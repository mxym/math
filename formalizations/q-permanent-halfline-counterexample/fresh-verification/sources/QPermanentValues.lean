import QPermanentDefs

namespace QPermanentHalfline

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Kernel reduction of the complete permutation sum over ℚ. -/
theorem rationalMatrix_value_49 :
    qPermanent rationalMatrix 49 = 81807513 / 500000 := by
  simp only [qPermanent]
  decide +kernel

theorem rationalMatrix_value_50 :
    qPermanent rationalMatrix 50 = 7969 / 50 := by
  simp only [qPermanent]
  decide +kernel

/-- The rational computation is transferred to the same matrix over ℝ. -/
theorem counterexampleMatrix_cast (q : ℚ) :
    qPermanent counterexampleMatrix (q : ℝ) = ((qPermanent rationalMatrix q : ℚ) : ℝ) := by
  exact qPermanent_map (Rat.castHom ℝ) rationalMatrix q

theorem counterexampleMatrix_value_49 :
    qPermanent counterexampleMatrix 49 = 81807513 / 500000 := by
  have h := counterexampleMatrix_cast 49
  norm_num only [Rat.cast_ofNat] at h
  rw [h, rationalMatrix_value_49]
  norm_num

theorem counterexampleMatrix_value_50 :
    qPermanent counterexampleMatrix 50 = 7969 / 50 := by
  have h := counterexampleMatrix_cast 50
  norm_num only [Rat.cast_ofNat] at h
  rw [h, rationalMatrix_value_50]
  norm_num

theorem counterexampleMatrix_exact_decrease :
    qPermanent counterexampleMatrix 49 - qPermanent counterexampleMatrix 50 =
      2117513 / 500000 := by
  rw [counterexampleMatrix_value_49, counterexampleMatrix_value_50]
  norm_num

theorem counterexampleMatrix_decreases :
    qPermanent counterexampleMatrix 50 < qPermanent counterexampleMatrix 49 := by
  rw [counterexampleMatrix_value_49, counterexampleMatrix_value_50]
  norm_num

end QPermanentHalfline
