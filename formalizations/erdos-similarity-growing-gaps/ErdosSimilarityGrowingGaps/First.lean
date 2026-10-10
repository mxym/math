import ErdosSimilarityGrowingGaps.Basic
namespace ErdosSimilarityGrowingGaps
open Filter

lemma exists_first_ge (Z : LogScale) (v : ℝ) :
    ∃ n : ℕ, v ≤ Z.z n ∧ ∀ m : ℕ, m < n → Z.z m < v := by
  have hex : ∃ n : ℕ, v ≤ Z.z n := by
    have hev : ∀ᶠ x : ℝ in atTop, v ≤ x := eventually_ge_atTop v
    have hz := Z.tendsto_atTop.eventually hev
    rcases (eventually_atTop.1 hz) with ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩
  let n : ℕ := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro m hm
  by_contra hnot
  have hvm : v ≤ Z.z m := le_of_not_gt hnot
  exact (Nat.find_min hex hm) hvm

end ErdosSimilarityGrowingGaps
