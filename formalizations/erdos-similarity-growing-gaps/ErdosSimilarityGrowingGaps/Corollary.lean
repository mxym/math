import ErdosSimilarityGrowingGaps.LogBounds

namespace ErdosSimilarityGrowingGaps
open Filter

/-- The paper's consecutive-gap hypothesis implies the annular filling
property.  The proof retains the endpoint sample explicitly, avoiding any
unstated maximum-gap convention. -/
theorem consecutiveGap_implies_annularFilling
    {Z : LogScale} (hgap : ConsecutiveLogGapLittleO Z) :
    AnnularFilling Z := by
  intro R hR η hη U₀ hU₀
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨N, hN⟩ := hgap ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (N ≤ n) ∧ (Real.exp 2 : ℝ) ≤ Z.z n ∧
        Real.exp (Real.exp (1 / η)) ≤ Z.z n ∧ U₀ / R ≤ Z.z n := by
    have hN' : ∀ᶠ n : ℕ in atTop, N ≤ n := eventually_ge_atTop N
    have he : ∀ᶠ n : ℕ in atTop, (Real.exp 2 : ℝ) ≤ Z.z n :=
      Z.tendsto_atTop.eventually (eventually_ge_atTop (Real.exp 2))
    have hη : ∀ᶠ n : ℕ in atTop,
        Real.exp (Real.exp (1 / η)) ≤ Z.z n :=
      Z.tendsto_atTop.eventually
        (eventually_ge_atTop (Real.exp (Real.exp (1 / η))))
    have hU : ∀ᶠ n : ℕ in atTop, U₀ / R ≤ Z.z n :=
      Z.tendsto_atTop.eventually (eventually_ge_atTop (U₀ / R))
    exact hN'.and (he.and (hη.and hU))
  obtain ⟨m, hmN, hmexp, hmη, hmU₀⟩ := hlarge.exists
  let U : ℝ := R * Z.z m
  let D : ℝ := η * Real.log (Real.log U)
  have hUpos : 0 < U := by
    dsimp [U]
    exact mul_pos hRpos (Z.positive m)
  have hz_m_pos : 0 < Z.z m := Z.positive m
  have hU_lower : U₀ ≤ U := by
    dsimp [U]
    have := (div_le_iff₀ hRpos).1 hmU₀
    nlinarith
  have hU_gt_one : 1 < U := by
    dsimp [U]
    have hR4 : (2 : ℝ) ≤ R := hRreal
    have hepos : 0 < Real.exp 2 := Real.exp_pos _
    have heone : 1 < Real.exp 2 := by
      have := Real.exp_pos 2
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by norm_num)
    nlinarith [hmexp]
  have hRlog : Real.log R ≤ Real.log U := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact hRpos
    · exact hUpos
    · dsimp [U]
      have heone : (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 (by norm_num)
      have hzmone : (1 : ℝ) ≤ Z.z m := le_trans heone.le hmexp
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hzmone hRpos.le
  have hUlog2 : (2 : ℝ) ≤ Real.log U := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    dsimp [U]
    have hRge : (1 : ℝ) ≤ R := by linarith
    have hzge : Real.exp 2 ≤ Z.z m := hmexp
    have : Real.exp 2 ≤ R * Z.z m := by nlinarith [hzge, hz_m_pos]
    exact this
  have hll : Real.log 2 ≤ Real.log (Real.log U) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact Real.log_pos hU_gt_one
    · exact hUlog2
  have hloglog_large : (1 / η : ℝ) ≤ Real.log (Real.log U) := by
    have hC : Real.exp (Real.exp (1 / η)) ≤ U := by
      dsimp [U]
      have hRge : (1 : ℝ) ≤ R := by linarith
      nlinarith [hmη, hz_m_pos]
    have hlogU_lower : Real.exp (1 / η) ≤ Real.log U := by
      apply (Real.le_log_iff_exp_le hUpos).2
      exact hC
    apply (Real.le_log_iff_exp_le (by linarith [hUlog2])).2
    simpa only [Real.exp_log (by positivity)] using hlogU_lower
  have hprod : η * (1 / η) = (1 : ℝ) := by
    field_simp
  have hDone : (1 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith [hη, hloglog_large, hprod]
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hDone
  have hanchor : AnnulusAnchor Z U R D := by
    have hquot : U / R = Z.z m := by
      dsimp [U]
      field_simp
    refine ⟨m, hquot.le, ?_⟩
    rw [hquot]
    linarith
  have hgap_local : GapBoundOn Z U R D := by
    intro n hnlo hnhi
    have hmn : m ≤ n := by
      by_contra hmn
      have hnm : n < m := Nat.lt_of_not_ge hmn
      have hzlt : Z.z n < Z.z m := Z.strictMono hnm
      have hquot : U / R = Z.z m := by
        dsimp [U]
        field_simp
      linarith
    have hNn : N ≤ n := hmN.trans hmn
    obtain ⟨hlogzn, hsmall⟩ := hN n hNn
    have hznpos : 0 < Z.z n := Z.positive n
    have hRUpos : 0 < R * U := by positivity
    have hlogzn_le : Real.log (Z.z n) ≤ Real.log (R * U) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact hznpos
      · exact hRUpos
      · exact hnhi
    have hloglogzn_pos : 0 < Real.log (Real.log (Z.z n)) := by
      exact Real.log_pos hlogzn
    have hlogRUpos : 0 < Real.log (R * U) := by
      exact Real.log_pos (by nlinarith [hRreal, hU_gt_one])
    have hloglog_bound : Real.log (Real.log (Z.z n)) ≤
        2 * Real.log (Real.log U) := by
      have hmono := Real.strictMonoOn_log.monotoneOn
        (by linarith : 0 < Real.log (Z.z n)) hlogRUpos hlogzn_le
      exact hmono.trans (loglog_mul_le_two hRreal hU_gt_one hRlog hll)
    dsimp [D, ε] at hsmall ⊢
    nlinarith
  have hfill := fillsAnnulus_of_anchor_gap hUpos hRreal hDone hanchor hgap_local
  exact ⟨U, D, hU_lower, hDone, le_rfl, hfill⟩

end ErdosSimilarityGrowingGaps
