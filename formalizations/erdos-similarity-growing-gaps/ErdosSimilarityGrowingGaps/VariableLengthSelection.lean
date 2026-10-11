import ErdosSimilarityGrowingGaps.VariableBridge

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! A generic joint choice for the finite template length.  The natural lower
bound `P` covers the geometric/base budget, while the logarithmic summand is
the entropy budget.  The hypotheses expose exactly the four sublinear terms
that are needed by the affine span estimate; no fixed-tree coefficient is
silently introduced. -/
theorem eventually_exists_joint_template_length
    {ι : Type*} {l : Filter ι}
    (A : ι → ℝ) (P : ι → ℕ) (B U : ι → ℝ)
    (hU : Tendsto U l atTop)
    (hA_nonneg : ∀ᶠ i in l, 0 ≤ A i)
    (hB_nonneg : ∀ᶠ i in l, 0 ≤ B i)
    (hAP : (fun i => A i * (P i : ℝ)) =o[l] U)
    (hALog : (fun i => A i * Real.log (U i + 2)) =o[l] U)
    (hA : A =o[l] U)
    (hB : B =o[l] U) :
    ∀ᶠ i in l, ∃ L : ℕ,
      P i ≤ L ∧ A i * (L : ℝ) + B i ≤ U i := by
  have hU_nonneg : ∀ᶠ i in l, 0 ≤ U i :=
    hU.eventually (eventually_ge_atTop (0 : ℝ))
  have hlog_nonneg : ∀ᶠ i in l, 0 ≤ Real.log (U i + 2) := by
    filter_upwards [hU_nonneg] with i hUi
    apply Real.log_nonneg
    linarith
  have hAP_bound := hAP.bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hALog_bound := hALog.bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hA_bound := hA.bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hB_bound := hB.bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hU_nonneg, hlog_nonneg, hA_nonneg, hB_nonneg,
    hAP_bound, hALog_bound, hA_bound, hB_bound] with i hUi hlog hAi hBi
      hAPi hALogi hAi' hBi'
  have hAPi' : A i * (P i : ℝ) ≤ (1 / 4 : ℝ) * U i := by
    have hnonneg : 0 ≤ A i * (P i : ℝ) :=
      mul_nonneg hAi (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Real.norm_eq_abs, abs_of_nonneg hUi] at hAPi
    exact hAPi
  have hALogi' : A i * Real.log (U i + 2) ≤ (1 / 4 : ℝ) * U i := by
    have hnonneg : 0 ≤ A i * Real.log (U i + 2) :=
      mul_nonneg hAi hlog
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Real.norm_eq_abs, abs_of_nonneg hUi] at hALogi
    exact hALogi
  have hAi'' : A i ≤ (1 / 4 : ℝ) * U i := by
    rw [Real.norm_eq_abs, abs_of_nonneg hAi,
      Real.norm_eq_abs, abs_of_nonneg hUi] at hAi'
    exact hAi'
  have hBi'' : B i ≤ (1 / 4 : ℝ) * U i := by
    rw [Real.norm_eq_abs, abs_of_nonneg hBi,
      Real.norm_eq_abs, abs_of_nonneg hUi] at hBi'
    exact hBi'
  let L : ℕ := P i + Nat.ceil (max (Real.log (U i + 2)) 0)
  have hP : P i ≤ L := by
    dsimp [L]
    exact Nat.le_add_right _ _
  have hmax : max (Real.log (U i + 2)) 0 = Real.log (U i + 2) :=
    max_eq_left hlog
  have hceil : (Nat.ceil (max (Real.log (U i + 2)) 0) : ℝ) ≤
      Real.log (U i + 2) + 1 := by
    rw [hmax]
    exact (Nat.ceil_lt_add_one hlog).le
  have hL : (L : ℝ) ≤ (P i : ℝ) + Real.log (U i + 2) + 1 := by
    dsimp [L]
    push_cast
    linarith
  have hscale : A i * (L : ℝ) ≤
      A i * (P i : ℝ) + A i * Real.log (U i + 2) + A i := by
    have hs := mul_le_mul_of_nonneg_left hL hAi
    nlinarith [hs]
  refine ⟨L, hP, ?_⟩
  nlinarith [hscale, hAPi', hALogi', hAi'', hBi'']

end ErdosSimilarityGrowingGaps
