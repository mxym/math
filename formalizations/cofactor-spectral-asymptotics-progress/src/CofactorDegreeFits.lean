import CofactorDegreeCount

/-! The explicit finite ring family is available in every sufficiently large integer dimension. -/
set_option autoImplicit false
open scoped BigOperators
open Filter
namespace CofactorSpectral
noncomputable section

theorem eventually_degreeCount_fits (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      let K := degreeCount b m δ N
      let d : Fin K → ℕ := fun k => ringDegreeSequence b m k.val
      let r := N-2*∑ k, d k
      0 < K ∧ 0 < r ∧ r+2*∑ k, d k = N ∧
        (2*∑ k, d k : ℕ) ≤ δ*(N : ℝ) ∧ 0 < Real.log (N : ℝ) := by
  have hl : 0 < Real.log b := Real.log_pos hb
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop,
      max 1 (Real.log b*(degreeLogOffset b m δ+1)) ≤ Real.log (N : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (he.and hN)
  refine ⟨N0,?_⟩
  intro N hNN
  obtain ⟨hlogLarge,hNN2⟩ := hN0 N hNN
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hlog : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_left _ _).trans hlogLarge)
  have hlogOffset : (degreeLogOffset b m δ+1)*Real.log b ≤ Real.log (N : ℝ) := by
    simpa only [mul_comm] using (le_max_right _ _).trans hlogLarge
  have hx : 1 ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ := by
    have h := (le_div_iff₀ hl).mpr hlogOffset
    linarith
  let K := degreeCount b m δ N
  let d : Fin K → ℕ := fun k => ringDegreeSequence b m k.val
  have hK : 0 < K := degreeCount_positive b m N δ hx
  have hs : (∑ k, d k) = ∑ k ∈ Finset.range K, ringDegreeSequence b m k :=
    Fin.sum_univ_eq_sum_range _ K
  have hx0 : 0 ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ := by linarith
  have hbudget := degreeCount_prefix_budget b hb m hm N hNp δ hδ0 hx0
  have hfrac : ((2*∑ k, d k : ℕ) : ℝ) ≤ δ*(N : ℝ) := by
    rw [hs,Nat.cast_mul,Nat.cast_ofNat]
    exact hbudget
  have hlt : 2*∑ k, d k < N := by
    have hp := mul_pos hNr (sub_pos.mpr hδ1)
    have h : ((2*∑ k, d k : ℕ) : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast h
  exact ⟨hK,Nat.sub_pos_of_lt hlt,Nat.sub_add_cancel hlt.le,hfrac,hlog⟩

end
end CofactorSpectral
