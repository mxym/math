import Entry002.Sieve

/-! Removing an actual finite initial interval does not change the literal
inclusive dyadic density: the counts are eventually exactly equal. -/
set_option autoImplicit false
namespace Entry002
open scoped Topology

/-- Above the cutoff, the actual two inclusive dyadic counts are equal. -/
theorem arithmeticSupply_dyadic_above_cutoff_eq (P : Set ℕ) (f : ℕ)
    (T : ℝ) (hT : (f : ℝ) < T) :
    dyadicPrimeCount {p | p ∈ P ∧ f < p} T = dyadicPrimeCount P T := by
  classical
  unfold dyadicPrimeCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hmem, ⟨hp, _⟩, hlow, hupp⟩
    exact ⟨hmem, hp, hlow, hupp⟩
  · rintro ⟨hmem, hp, hlow, hupp⟩
    refine ⟨hmem, ⟨hp, ?_⟩, hlow, hupp⟩
    exact_mod_cast hT.trans_le hlow

/-- A finite initial prime exclusion preserves the actual positive natural
dyadic limit without any analytic premise beyond that limit itself. -/
theorem arithmeticSupply_dyadic_above_cutoff (P : Set ℕ) (f : ℕ) (ρ : ℝ)
    (h : Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ)) :
    Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount {p | p ∈ P ∧ f < p} T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ) := by
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (f : ℝ)] with T hT
  rw [arithmeticSupply_dyadic_above_cutoff_eq P f T hT]

end Entry002
