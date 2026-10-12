import ErdosSimilarityGrowingGaps.GreedySampling

namespace ErdosSimilarityGrowingGaps

/-! A finite prefix bound also controls every later greedy slot.  This is the
tail fact needed when a greedy anchor is selected from an annulus: the proof
uses only the first-ge specification and the lower greedy crossing property. -/
theorem greedyIndex_tail_of_prefix_bound
    {Z : LogScale} (v δ A : ℝ) (N : ℕ) (hδ : 0 < δ)
    (hA : A ≤ v)
    (hprefix : ∀ m : ℕ, m < N → Z.z m < A) :
    ∀ i : ℕ, N ≤ greedyIndex Z v δ i := by
  intro i
  by_contra hN
  have hlt : greedyIndex Z v δ i < N := Nat.lt_of_not_ge hN
  have hzlt : Z.z (greedyIndex Z v δ i) < A := hprefix _ hlt
  have hzge : v ≤ Z.z (greedyIndex Z v δ i) :=
    greedyIndex_first_log_ge Z v δ hδ i
  linarith

theorem greedyIndex_tail_of_integer_prefix
    {Z : LogScale} (v δ : ℝ) (N B : ℕ) (hδ : 0 < δ)
    (hB : (B : ℝ) ≤ v)
    (hprefix : ∀ m : ℕ, m < N → Z.z m < (B : ℝ)) :
    ∀ i : ℕ, N ≤ greedyIndex Z v δ i := by
  apply greedyIndex_tail_of_prefix_bound v δ (B : ℝ) N hδ hB
  exact hprefix

end ErdosSimilarityGrowingGaps
