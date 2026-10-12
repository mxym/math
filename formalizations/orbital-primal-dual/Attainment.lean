import SharpResponse
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

theorem isClosed_probability : IsClosed {p : I → ℝ | Probability p} := by
  have hnonneg : IsClosed {p : I → ℝ | ∀ i, 0 ≤ p i} := by
    have h := isClosed_iInter (fun i : I =>
      isClosed_le (continuous_const : Continuous (fun _ : I → ℝ => (0 : ℝ)))
        (continuous_apply i))
    convert h using 1
    ext p
    simp
  have hsum : IsClosed {p : I → ℝ | ∑ i, p i = 1} := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  exact hnonneg.inter hsum

theorem probability_subset_cube : {p : I → ℝ | Probability p} ⊆
    Icc (0 : I → ℝ) 1 := by
  intro p hp
  constructor
  · exact hp.1
  · intro i
    calc
      p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      _ = 1 := hp.2

theorem isCompact_probability : IsCompact {p : I → ℝ | Probability p} :=
  (isCompact_Icc : IsCompact (Icc (0 : I → ℝ) 1)).of_isClosed_subset
    isClosed_probability probability_subset_cube

def feasiblePairs (A : J → I → ℝ) : Set ((I → ℝ) × (I → ℝ)) :=
  {pq | Probability pq.1 ∧ Probability pq.2 ∧ Match A pq.1 pq.2}

theorem isClosed_feasiblePairs (A : J → I → ℝ) : IsClosed (feasiblePairs A) := by
  have hp := isClosed_probability.preimage
    (continuous_fst : Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.1))
  have hq := isClosed_probability.preimage
    (continuous_snd : Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.2))
  have hm : IsClosed {pq : (I → ℝ) × (I → ℝ) | Match A pq.1 pq.2} := by
    have h := isClosed_iInter fun j : J =>
      isClosed_eq
        (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => ∑ i, A j i * pq.1 i) by
          fun_prop)
        (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => ∑ i, A j i * pq.2 i) by
          fun_prop)
    convert h using 1
    ext pq
    simp [Match]
  exact hp.inter (hq.inter hm)

theorem isCompact_feasiblePairs (A : J → I → ℝ) : IsCompact (feasiblePairs A) := by
  exact (isCompact_probability.prod isCompact_probability).of_isClosed_subset
    (isClosed_feasiblePairs A) (fun _ h => ⟨h.1, h.2.1⟩)

variable [Nonempty I]

theorem feasiblePairs_nonempty (A : J → I → ℝ) : (feasiblePairs A).Nonempty :=
  ⟨(uniform, uniform), uniform_probability, uniform_probability, fun _ => rfl⟩

theorem exists_optimal_pair (A : J → I → ℝ) (i : I) :
    ∃ p q : I → ℝ, Probability p ∧ Probability q ∧ Match A p q ∧
      0 ≤ p i - q i ∧ PairBound A i (p i - q i) := by
  obtain ⟨pq, hpq, hmax⟩ := (isCompact_feasiblePairs A).exists_isMaxOn
    (feasiblePairs_nonempty A)
    (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.1 i - pq.2 i) by
      fun_prop).continuousOn
  refine ⟨pq.1, pq.2, hpq.1, hpq.2.1, hpq.2.2, ?_, ?_⟩
  · have h0 := hmax (show (uniform, uniform) ∈ feasiblePairs A from
      ⟨uniform_probability, uniform_probability, fun _ => rfl⟩)
    change uniform i - uniform i ≤ pq.1 i - pq.2 i at h0
    simpa only [sub_self] using h0
  · intro p q hp hq hm
    exact hmax (show (p, q) ∈ feasiblePairs A from ⟨hp, hq, hm⟩)

theorem exists_sharp_uniform_response (A : J → I → ℝ) (i : I) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 1 ∧ UniformLawBound A i C ∧
      ∀ D : ℝ, 0 ≤ D → UniformLawBound A i D → C ≤ D := by
  obtain ⟨p, q, hp, hq, hm, hC, hbound⟩ := exists_optimal_pair A i
  refine ⟨p i - q i, hC, ?_,
    (uniformLawBound_iff_pairBound A i _ hC).mpr hbound, ?_⟩
  · have hpi : p i ≤ 1 := (probability_subset_cube hp).2 i
    linarith [hq.1 i]
  · intro D hD hb
    exact (uniformLawBound_iff_pairBound A i D hD).mp hb p q hp hq hm

end
end OrbitalMarginals
