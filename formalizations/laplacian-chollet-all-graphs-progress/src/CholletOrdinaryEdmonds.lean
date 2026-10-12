import CholletMatchingDouble

set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy

namespace Chollet
namespace Matching

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
noncomputable section

def projectMatching (G : LooplessGraph V E) (M : (doubled G).Matching) :
    OrdinaryMatching G :=
  ⟨Finset.univ.filter (fun e => Sum.inl (e, false) ∈ M.val), by
    intro v e f he hf hve hvf
    obtain ⟨a, ha, hu⟩ := M.property (v, false)
    have he' : (doubled G).Incident (v, false) (.inl (e, false)) := by
      simpa [LooplessGraph.Incident, doubled] using hve
    have hf' : (doubled G).Incident (v, false) (.inl (f, false)) := by
      simpa [LooplessGraph.Incident, doubled] using hvf
    have hh := (hu (.inl (e, false)) ⟨(Finset.mem_filter.mp he).2, he'⟩).trans
      (hu (.inl (f, false)) ⟨(Finset.mem_filter.mp hf).2, hf'⟩).symm
    exact congrArg Prod.fst (Sum.inl.inj hh)⟩

@[simp] theorem mem_projectMatching (G : LooplessGraph V E)
    (M : (doubled G).Matching) (e : E) :
    e ∈ (projectMatching G M).val ↔ Sum.inl (e, false) ∈ M.val := by
  simp [projectMatching]

theorem doubled_card_even : Even (Fintype.card (V × Bool)) := by
  simp only [Fintype.card_prod, Fintype.card_bool]
  exact ⟨Fintype.card V, by omega⟩

/-- A feasible ordinary matching vector is the edge marginal of an actual
finite probability law, indexed by perfect matchings of the doubled graph. -/
theorem ordinary_matching_law (G : LooplessGraph V E) (x : E → ℝ)
    (hx : OrdinaryFeasible G x) :
    ∃ p : (doubled G).Matching → ℝ,
      (∀ M, 0 ≤ p M) ∧ (∑ M, p M = 1) ∧
      ∀ e, (∑ M, p M * (if e ∈ (projectMatching G M).val then 1 else 0)) = x e := by
  obtain ⟨p, hp, hm, he⟩ := CholletAssessment.edmonds_perfect_matching_distribution
    (doubled G) doubled_card_even (doubledWeights G x) (doubled_feasible G x hx)
  refine ⟨p, hp, hm, fun e => ?_⟩
  have h := congrFun he (Sum.inl (e, false))
  simpa [LooplessGraph.mean, LooplessGraph.indicator, doubledWeights] using h

/-- The ordinary Edmonds weighted-matching consequence for arbitrary real
weights. Every edge in the output is an actual matching edge. -/
theorem exists_matching_weight_ge (G : LooplessGraph V E) (x w : E → ℝ)
    (hx : OrdinaryFeasible G x) :
    ∃ M : OrdinaryMatching G, (∑ e, x e * w e) ≤ ∑ e ∈ M.val, w e := by
  obtain ⟨p, hp, hm, he⟩ := ordinary_matching_law G x hx
  have hn : (Finset.univ : Finset (doubled G).Matching).Nonempty := by
    by_contra h
    have hz : (Finset.univ : Finset (doubled G).Matching) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.sum_empty] at hm
    norm_num at hm
  let score (M : (doubled G).Matching) : ℝ := ∑ e ∈ (projectMatching G M).val, w e
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image Finset.univ score hn
  refine ⟨projectMatching G M, ?_⟩
  have havg : (∑ N, p N * score N) = ∑ e, x e * w e := by
    have hscore (N : (doubled G).Matching) : score N =
        ∑ e, (if e ∈ (projectMatching G N).val then (1 : ℝ) else 0) * w e := by
      simp only [score, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp [projectMatching]
    simp_rw [hscore, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he'
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, he]
  rw [← havg]
  calc
    _ ≤ ∑ N, p N * score M := Finset.sum_le_sum fun N hN =>
      mul_le_mul_of_nonneg_left (hmax N hN) (hp N)
    _ = score M := by rw [← Finset.sum_mul, hm, one_mul]

end
end Matching
end Chollet
