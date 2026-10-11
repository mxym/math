import APPTReview.AllDimensionUpper

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReviewFixedLocalChecks

/-- An actual APPT family rejects replacing m^2/(m^2-1) by one or 1+1/m^2. -/
theorem qubit_plateau_rejects_wrong_coefficient :
    ∃ A : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      (8:ℝ)*APPT.Quantum.purity A=4/3 ∧ (5:ℝ)/4<8*APPT.Quantum.purity A := by
  obtain ⟨A,hd,ha,hp⟩ := APPTReview.exists_projectionPlateau
    (m:=2) (n:=4) (by omega) (by omega) 2 (by omega)
  refine ⟨A,hd,ha,?_,?_⟩
  all_goals rw [hp]; norm_num [APPTReview.plateauDenominator]

/-- A physical odd-rounding example rejects identifying the finite candidate
with its continuous-rank limit. The exact gap is positive, not a tolerance. -/
theorem odd_rank_rounding_gap :
    ∃ A : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      (16:ℝ)/15-20*APPT.Quantum.purity A=1/5415 := by
  obtain ⟨A,hd,ha,hp⟩ := APPTReview.exists_projectionPlateau
    (m:=4) (n:=5) (by omega) (by omega) 8 (by omega)
  refine ⟨A,hd,ha,?_⟩
  rw [hp]
  norm_num [APPTReview.plateauDenominator]

/-- The interval secant constant is strictly larger than a falsely unit bound. -/
theorem interval_constant_rejects_one : (3+1:ℝ)^2/(4*3)>1 := by norm_num

end APPTReviewFixedLocalChecks
