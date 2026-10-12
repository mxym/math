import Counterexample

open scoped BigOperators
open MutualInformationCounterexample

namespace IndependentLiteralSemantics

noncomputable def tableP (e : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(1-e)/2, 0, 0], ![0, (1-e)/2, 0], ![0, 0, e]]
noncomputable def tableQ (e : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(1-e)/2, e/2, 0], ![e/2, (1-e)/2, 0], ![0, 0, 0]]
def probability (p : Fin 3 → Fin 3 → ℝ) : Prop :=
  (∀ i j, 0 ≤ p i j) ∧ (∑ i, ∑ j, p i j) = 1
def row (p : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ := ∑ j, p i j
def column (p : Fin 3 → Fin 3 → ℝ) (j : Fin 3) : ℝ := ∑ i, p i j
noncomputable def shannon {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, -(p i) * Real.log (p i)
noncomputable def information (p : Fin 3 → Fin 3 → ℝ) : ℝ :=
  shannon (row p) + shannon (column p) - ∑ i, shannon (p i)
noncomputable def variation (p q : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (∑ i, ∑ j, |p i j - q i j|) / 2
noncomputable def h (e : ℝ) : ℝ :=
  -e * Real.log e - (1-e) * Real.log (1-e)

example (e : ℝ) (he : 0 < e) (h16 : e ≤ 1/16) :
    probability (tableP e) ∧ probability (tableQ e) ∧
    variation (tableP e) (tableQ e) = e ∧
    h e + e * Real.log 8 < |information (tableP e) - information (tableQ e)| := by
  simpa only [probability, tableP, tableQ, variation, h, information, shannon,
    row, column, IsProbability, P, Q, totalVariation, binaryEntropy,
    mutualInformation, entropy, jointEntropy, marginalA, marginalB, eta,
    sub_eq_add_neg, neg_mul] using counterexample_family e he h16

example (r : ℝ) (hr : 0 < r) :
    ∃ (p q : Fin 3 → Fin 3 → ℝ) (e : ℝ),
      probability p ∧ probability q ∧ 0 < e ∧ e < r ∧ variation p q = e ∧
      h e + e * Real.log 8 < |information p - information q| := by
  simpa only [probability, variation, h, information, shannon, row, column,
    IsProbability, totalVariation, binaryEntropy, mutualInformation,
    entropy, jointEntropy, marginalA, marginalB, eta, sub_eq_add_neg, neg_mul]
    using counterexamples_arbitrarily_close r hr

example (e : ℝ) (he : 0 < e) :
    marginalA (P e) ≠ marginalA (Q e) ∧ marginalB (P e) ≠ marginalB (Q e) := by
  constructor
  · intro same
    have coordinate := congrFun same (2 : Fin 3)
    have zero : e = 0 := by simpa [P_marginalA, Q_marginalA] using coordinate
    exact (ne_of_gt he) zero
  · intro same
    have coordinate := congrFun same (2 : Fin 3)
    have zero : e = 0 := by simpa [P_marginalB, Q_marginalB] using coordinate
    exact (ne_of_gt he) zero

#check @counterexample_family
#check @proposed_classical_bound_false
#check @counterexamples_arbitrarily_close
#print axioms counterexample_family
#print axioms proposed_classical_bound_false
#print axioms counterexamples_arbitrarily_close

end IndependentLiteralSemantics
