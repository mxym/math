import APPTReview.IntegerPlateau

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The scalar rank objective agrees with the purity of each actual projection state. -/
theorem projectionPlateau_scaled_purity {m n : ℕ} (k : ℕ)
    (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hsq : P*P=P) (htr : P.trace=(k:ℂ)) :
    ((m:ℝ)*n)*APPT.Quantum.purity (projectionPlateau k P)=plateauScaledPurity m n k := by
  rw [projectionPlateau_purity k P hsq htr]
  rfl

/-- The complete integer-rank projection family has a physically attained maximum,
and equality in that family forces the exact ceiling rank. This is deliberately
not stated as an upper bound on all APPT density matrices. -/
theorem exists_projection_family_unique_rank_max {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    let t := ((m-1)*n+1)/2
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      ((m:ℝ)*n)*APPT.Quantum.purity A=plateauScaledPurity m n t ∧
      ∀ (k : ℕ) (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
        P.IsHermitian → P*P=P → P.trace=(k:ℂ) →
        APPT.Quantum.purity (projectionPlateau k P) ≤ APPT.Quantum.purity A ∧
        (APPT.Quantum.purity (projectionPlateau k P)=APPT.Quantum.purity A ↔ k=t) := by
  dsimp only
  let t := ((m-1)*n+1)/2
  have hn : 0 < n := by omega
  have ht : t ≤ m*n := by
    have hm1 : m-1+1=m := by omega
    have he : (m-1)*n+1 ≤ m*n := by nlinarith
    exact (Nat.div_le_self _ _).trans he
  obtain ⟨A,hA,happt,hpur⟩ := exists_projectionPlateau hm hn t ht
  have hscaled : ((m:ℝ)*n)*APPT.Quantum.purity A=plateauScaledPurity m n t := by
    rw [hpur]
    rfl
  have hD : (0:ℝ) < (m:ℝ)*n := by
    have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  refine ⟨A,hA,happt,hscaled,?_⟩
  intro k P hP hsq htr
  have hp := projectionPlateau_scaled_purity k P hsq htr
  have hopt := plateauScaledPurity_ceiling_unique hm hn k
  change plateauScaledPurity m n k ≤ plateauScaledPurity m n t ∧
    (plateauScaledPurity m n k=plateauScaledPurity m n t ↔ k=t) at hopt
  rw [← hp,← hscaled] at hopt
  refine ⟨(mul_le_mul_iff_right₀ hD).mp hopt.1,?_⟩
  constructor
  · intro he
    exact hopt.2.mp (congrArg (fun x : ℝ => ((m:ℝ)*n)*x) he)
  · intro he
    exact mul_left_cancel₀ (ne_of_gt hD) (hopt.2.mpr he)

/-- The floor is strictly wrong in this odd-parity case. -/
theorem plateau_odd_rounding_regression :
    plateauScaledPurity 4 5 8-plateauScaledPurity 4 5 7=5/494209 := by
  norm_num [plateauScaledPurity,plateauDenominator]

end APPTReview
