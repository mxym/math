import APPTReview.EightLower
import APPTReview.WideAsymptotic

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

noncomputable def sharpPurityCoefficient (m n : ℕ) : ℝ :=
  max 8 (broadBranchCoefficient m n)

/-- A single total-dimension threshold gives the sharp lower coefficient over
all physical dimensions. The hierarchy is fixed before the dimension threshold;
small first factors are handled by the already verified broad-plateau branch. -/
theorem appt_total_dimension_sharp_lower (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ m n : ℕ, 2≤m → m≤n → N≤m*n →
      ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
        (1-ε)*sharpPurityCoefficient m n≤
          ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  obtain ⟨M,hM2,hM⟩ := appt_growing_dimension_eight_lower (8*ε) (by positivity)
  obtain ⟨L,hL⟩ := appt_total_dimension_branch_lower ε hε
  refine ⟨max L (4*M^2),?_⟩
  intro m n hm hmn hN
  by_cases hb : 8≤broadBranchCoefficient m n
  · obtain ⟨A,hA,hP,hlo⟩ := hL m n hm hmn ((le_max_left _ _).trans hN)
    refine ⟨A,hA,hP,?_⟩
    rw [sharpPurityCoefficient,max_eq_right hb]
    exact hlo
  · have hmM : M≤m := by
      by_contra hsmall
      have hmR : (2:ℝ)≤m := by exact_mod_cast hm
      have hml : (m:ℝ)≤M := by exact_mod_cast (show m≤M by omega)
      have hsq : (m:ℝ)^2≤(M:ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hml 2
      have hD : 4*(M:ℝ)^2≤(m:ℝ)*n := by
        exact_mod_cast (show 4*M^2≤m*n from (le_max_right _ _).trans hN)
      have hden : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
      have hr : (4:ℝ)≤((m:ℝ)*n)/((m:ℝ)^2-1) :=
        (le_div_iff₀ hden).2 (by nlinarith)
      apply hb
      unfold broadBranchCoefficient
      linarith
    obtain ⟨A,hA,hP,hlo⟩ := hM m n hmM hmn
    refine ⟨A,hA,hP,?_⟩
    rw [sharpPurityCoefficient,max_eq_left (le_of_not_ge hb)]
    linarith

/-- Both sides concern the original physical purity supremum, already proved
attained. No independent spectral ansatz is included among the hypotheses. -/
theorem appt_sharp_sup_two_sided (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ m n : ℕ, 2≤m → m≤n → N≤m*n →
      (1-ε)*sharpPurityCoefficient m n≤excessPuritySup m n ∧
      excessPuritySup m n≤(1+ε)*sharpPurityCoefficient m n := by
  obtain ⟨L,hL⟩ := appt_total_dimension_sharp_lower ε hε
  obtain ⟨U,hU⟩ := appt_total_dimension_uniform_upper ε hε
  refine ⟨max L U,?_⟩
  intro m n hm hmn hN
  obtain ⟨A,hA,hP,hlo⟩ := hL m n hm hmn ((le_max_left _ _).trans hN)
  have hs : APPT.Quantum.purity A≤apptPuritySup m n :=
    (appt_purity_sup_isGreatest hm hmn).2 ⟨A,hA,hP,rfl⟩
  refine ⟨hlo.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hs _) (sq_nonneg _)),?_⟩
  obtain ⟨B,hB,hQ,hmax⟩ := exists_appt_purity_eq_sup hm hmn
  have hu := hU m n hm hmn ((le_max_right _ _).trans hN) B hB hQ
  rw [hmax] at hu
  exact hu

end APPTReview
