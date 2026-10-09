import CholletSmallBlocks
import CholletOrdinaryEdmonds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial BapatFiniteRank OAI.MatchingEntropy

namespace Chollet
namespace Matching

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
noncomputable section

def unmatched (G : LooplessGraph V E) (M : OrdinaryMatching G) : Finset V :=
  Finset.univ.filter fun v => ¬∃ e ∈ M.val, G.Incident v e

def matchingParts (G : LooplessGraph V E) (M : OrdinaryMatching G) : Finset (E ⊕ V) :=
  M.val.disjSum (unmatched G M)

def matchingBlock (G : LooplessGraph V E) : E ⊕ V → Finset V
  | .inl e => {G.left e, G.right e}
  | .inr v => {v}

@[simp] theorem mem_matchingBlock_edge (G : LooplessGraph V E) (v : V) (e : E) :
    v ∈ matchingBlock G (.inl e) ↔ G.Incident v e := by
  simp [matchingBlock, LooplessGraph.Incident, eq_comm]

theorem matchingBlocks_disjoint (G : LooplessGraph V E) (M : OrdinaryMatching G) :
    (matchingParts G M : Set (E ⊕ V)).PairwiseDisjoint (matchingBlock G) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  cases a with
  | inl e =>
    have he : e ∈ M.val := by simpa [matchingParts] using ha
    have hve := (mem_matchingBlock_edge G v e).mp hva
    cases b with
    | inl f =>
      have hf : f ∈ M.val := by simpa [matchingParts] using hb
      have hvf := (mem_matchingBlock_edge G v f).mp hvb
      exact hab (congrArg Sum.inl (M.property v e f he hf hve hvf))
    | inr w =>
      have hw : ¬∃ f ∈ M.val, G.Incident w f := by simpa [matchingParts, unmatched] using hb
      have hvw : v = w := by simpa [matchingBlock] using hvb
      subst w
      exact hw ⟨e, he, hve⟩
  | inr u =>
    have hu : ¬∃ e ∈ M.val, G.Incident u e := by simpa [matchingParts, unmatched] using ha
    have hvu : v = u := by simpa [matchingBlock] using hva
    subst u
    cases b with
    | inl f =>
      have hf : f ∈ M.val := by simpa [matchingParts] using hb
      exact hu ⟨f, hf, (mem_matchingBlock_edge G v f).mp hvb⟩
    | inr w =>
      have hvw : v = w := by simpa [matchingBlock] using hvb
      exact hab (congrArg Sum.inr hvw)

theorem matchingBlocks_cover (G : LooplessGraph V E) (M : OrdinaryMatching G) :
    (matchingParts G M).biUnion (matchingBlock G) = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true, Finset.mem_biUnion]
  by_cases h : ∃ e ∈ M.val, G.Incident v e
  · obtain ⟨e, he, hve⟩ := h
    exact ⟨.inl e, by simpa [matchingParts] using he,
      (mem_matchingBlock_edge G v e).mpr hve⟩
  · exact ⟨.inr v, by simpa [matchingParts, unmatched] using h, by simp [matchingBlock]⟩

theorem matchingBlocks_small (G : LooplessGraph V E) (a : E ⊕ V) :
    (matchingBlock G a).card ≤ 2 := by
  cases a with
  | inl e => exact Finset.card_le_two
  | inr v => simp [matchingBlock]

theorem permanent_psd_matching (G : LooplessGraph V E) (M : OrdinaryMatching G)
    (A : Matrix V V ℝ) (hA : A.PosSemidef) :
    (∏ e ∈ M.val, (A (G.left e) (G.left e) * A (G.right e) (G.right e) +
      (A (G.left e) (G.right e))^2)) * (∏ v ∈ unmatched G M, A v v) ≤ A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have ha : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  have h := product_small_blocks_norm_bound v (matchingParts G M) (matchingBlock G)
    (fun a _ => matchingBlocks_small G a)
  have hp : (∏ a ∈ matchingParts G M, formsOn v (matchingBlock G a)) = formsProduct v := by
    unfold formsOn formsProduct
    rw [← Finset.prod_biUnion (matchingBlocks_disjoint G M), matchingBlocks_cover]
  rw [hp, ← permanent_gram_eq, ← ha] at h
  have hb (a : E ⊕ V) : fischerPair (formsOn v (matchingBlock G a))
      (formsOn v (matchingBlock G a)) = match a with
      | .inl e => A (G.left e) (G.left e) * A (G.right e) (G.right e) +
          (A (G.left e) (G.right e))^2
      | .inr u => A u u := by
    cases a with
    | inl e =>
      simp [matchingBlock, formsOn, G.loopless e, pair_quadratic_self, ← hv]
    | inr u => simp [matchingBlock, formsOn, pair_linearForm_self, ← hv]
  simp_rw [hb] at h
  simpa [matchingParts] using h

theorem permanent_unit_diag_matching (G : LooplessGraph V E) (M : OrdinaryMatching G)
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (hd : ∀ v, A v v = 1) :
    (∏ e ∈ M.val, (1 + (A (G.left e) (G.right e))^2)) ≤ A.permanent := by
  simpa [hd] using permanent_psd_matching G M A hA

theorem log_permanent_ge_matching (G : LooplessGraph V E) (M : OrdinaryMatching G)
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (hd : ∀ v, A v v = 1) :
    (∑ e ∈ M.val, Real.log (1 + (A (G.left e) (G.right e))^2)) ≤ Real.log A.permanent := by
  have hpos (e : E) : 0 < 1 + (A (G.left e) (G.right e))^2 := by positivity
  have h := Real.log_le_log (Finset.prod_pos (fun e _ => hpos e))
    (permanent_unit_diag_matching G M A hA hd)
  rwa [Real.log_prod (fun e _ => (hpos e).ne')] at h

theorem log_permanent_ge_fractional (G : LooplessGraph V E) (x : E → ℝ)
    (hx : OrdinaryFeasible G x) (A : Matrix V V ℝ) (hA : A.PosSemidef)
    (hd : ∀ v, A v v = 1) :
    (∑ e, x e * Real.log (1 + (A (G.left e) (G.right e))^2)) ≤ Real.log A.permanent := by
  obtain ⟨M, hM⟩ := exists_matching_weight_ge G x
    (fun e => Real.log (1 + (A (G.left e) (G.right e))^2)) hx
  exact hM.trans (log_permanent_ge_matching G M A hA hd)

theorem log_one_add_ge_eight_ninths {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    (8 / 9 : ℝ) * t ≤ Real.log (1 + t) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg ht)
  apply (le_div_iff₀ (by linarith : 0 < t + 2)).mpr
  nlinarith

/-- Numerical endpoint of the normalized noncycle argument. Feasibility is
an explicit hypothesis here and still has to be proved for the actual graph. -/
theorem normalized_log_permanent_lower (G : LooplessGraph V E)
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (hd : ∀ v, A v v = 1)
    (hs : ∀ e, (A (G.left e) (G.right e))^2 ≤ 1 / 4)
    (hx : OrdinaryFeasible G (fun e => (9 / 5 : ℝ) * (A (G.left e) (G.right e))^2)) :
    (8 / 5 : ℝ) * (∑ e, ((A (G.left e) (G.right e))^2)^2) ≤ Real.log A.permanent := by
  apply le_trans _ (log_permanent_ge_fractional G _ hx A hA hd)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have h := mul_le_mul_of_nonneg_left
    (log_one_add_ge_eight_ninths (sq_nonneg _) (hs e))
    (show 0 ≤ (9 / 5 : ℝ) * (A (G.left e) (G.right e))^2 by positivity)
  nlinarith

end
end Matching
end Chollet
