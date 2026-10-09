import CofactorLargeDimensionWitness

/-! The actual four extrema have every-large-dimension lower bounds for each fixed parameter set. -/
set_option autoImplicit false
open scoped BigOperators
open Filter
namespace CofactorSpectral
noncomputable section

theorem degreeCount_eventual_log_lower (b : ℝ) (hb : 1 < b) (m : ℕ) (δ D ε : ℝ)
    (hD : 0 < D) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      1/(D*Real.log b)-ε ≤ ((degreeCount b m δ N : ℝ)/D)/Real.log (N : ℝ) ∧
        0 < Real.log (N : ℝ) := by
  have hl : 0 < Real.log b := Real.log_pos hb
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop,
      max 1 (|degreeLogOffset b m δ+1|/(D*ε)) ≤ Real.log (N : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨N0,?_⟩
  intro N hN
  have hlarge := hN0 N hN
  have hlog : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_left _ _).trans hlarge)
  have herr : degreeLogOffset b m δ+1 ≤ ε*D*Real.log (N : ℝ) := by
    have h := (div_le_iff₀ (mul_pos hD hε)).mp ((le_max_right _ _).trans hlarge)
    have ha := le_abs_self (degreeLogOffset b m δ+1)
    nlinarith
  have hf := degreeCount_lower b m N δ
  refine ⟨?_,hlog⟩
  apply (le_div_iff₀ hlog).2
  apply (le_div_iff₀ hD).2
  calc
    _ = Real.log (N : ℝ)/Real.log b-ε*D*Real.log (N : ℝ) := by
      field_simp [hD.ne',hl.ne']
      <;> ring
    _ ≤ Real.log (N : ℝ)/Real.log b-(degreeLogOffset b m δ+1) := by linarith
    _ ≤ _ := by linarith

theorem four_extrema_eventual_fixed_log_lower (C b δ η ε : ℝ) (hC : 0 < C) (hb : 1 < b)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hε : 0 < ε)
    (hθ : entropyConstant b/(C*Real.exp 1*(1-δ)) < 1) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      1/(C*(1+η)*Real.log b)-ε ≤ complexExtremum N/Real.log (N : ℝ) ∧
      (1/(C*(1+η)*Real.log b)-ε)/2 ≤ realExtremum N/Real.log (N : ℝ) ∧
      1/(C*(1+η)*Real.log b)-ε ≤ rankTwoComplexExtremum N/Real.log (N : ℝ) ∧
      (1/(C*(1+η)*Real.log b)-ε)/2 ≤ rankTwoRealExtremum N/Real.log (N : ℝ) := by
  obtain ⟨m,hm,N0,hN0⟩ := eventually_four_extrema_degree_lower C b δ η hC hb hδ0 hδ1 hη hθ
  have hD : 0 < C*(1+η) := mul_pos hC (by linarith)
  obtain ⟨N1,hN1⟩ := degreeCount_eventual_log_lower b hb m δ (C*(1+η)) ε hD hε
  refine ⟨max N0 N1,?_⟩
  intro N hN
  obtain ⟨hc,hr,hc2,hr2⟩ := hN0 N ((le_max_left _ _).trans hN)
  obtain ⟨hd,hlog⟩ := hN1 N ((le_max_right _ _).trans hN)
  have hdHalf := div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 2)
  have he : ((degreeCount b m δ N : ℝ)/(2*C*(1+η)))/Real.log (N : ℝ) =
      (((degreeCount b m δ N : ℝ)/(C*(1+η)))/Real.log (N : ℝ))/2 := by
    have hT : 1+η ≠ 0 := by linarith
    field_simp [hC.ne',hlog.ne',hT]
    <;> ring
  have hrn := div_le_div_of_nonneg_right hr hlog.le
  have hr2n := div_le_div_of_nonneg_right hr2 hlog.le
  rw [he] at hrn hr2n
  exact ⟨hd.trans (div_le_div_of_nonneg_right hc hlog.le),hdHalf.trans hrn,
    hd.trans (div_le_div_of_nonneg_right hc2 hlog.le),hdHalf.trans hr2n⟩

end
end CofactorSpectral
