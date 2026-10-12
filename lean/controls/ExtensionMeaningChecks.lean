import Mxym
open scoped BigOperators Classical
open Mxym.Rademacher

namespace ExtensionAudit
noncomputable section

-- Explicit reductions for the finite sign enumeration; all are definitional equalities.
private theorem cons_two {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 2) → α) :
    Fin.cons (α := fun _ : Fin (n + 3) => α) a f 2 = f 1 := rfl
private theorem cons_three {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 3) → α) :
    Fin.cons (α := fun _ : Fin (n + 4) => α) a f 3 = f 2 := rfl
private theorem cons_four {n : ℕ} {α : Type*} (a : α) (f : Fin (n + 4) → α) :
    Fin.cons (α := fun _ : Fin (n + 5) => α) a f 4 = f 3 := rfl

def three : Fin 3 → ℝ := ![1/3, 1/3, 1/3]
def noMassNormalization : Fin 4 → ℝ := fun _ => 1/2
def negativeCoefficient : Fin 5 → ℝ := ![1/2, 1/2, 1/2, 1/2, -1]
def falseGap : Fin 4 → ℝ := ![1/2, 1/6, 1/6, 1/6]
def falseFourthLowerBound : Fin 4 → ℝ := ![1/3, 1/3, 1/3, 0]

theorem three_mean : mean three = 1/2 := by
  norm_num [three, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, cons_four, Fin.default_eq_zero]
theorem noMassNormalization_mean : mean noMassNormalization = 3/4 := by
  norm_num [noMassNormalization, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, cons_four, Fin.default_eq_zero]
theorem negativeCoefficient_mean : mean negativeCoefficient = 9/8 := by
  norm_num [negativeCoefficient, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, cons_four, Fin.default_eq_zero]
theorem falseGap_mean : mean falseGap = 1/2 := by
  norm_num [falseGap, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, cons_four, Fin.default_eq_zero]
theorem falseFourthLowerBound_mean : mean falseFourthLowerBound = 1/2 := by
  norm_num [falseFourthLowerBound, mean, signedSum, sum_signs_succ, Fin.sum_univ_succ,
    sign, cons_two, cons_three, cons_four, Fin.default_eq_zero]

-- Verify the counterexamples satisfy the other material hypotheses.
theorem three_balanced : three ∈ balancedPolytope := by
  constructor
  · intro i; fin_cases i <;> norm_num [three]
  · norm_num [three, Fin.sum_univ_succ]

example : (∀ i, three i ≤ (1/2 : ℝ) - 1/6) ∧ ¬ Nonempty (Fin 4 ↪ Fin 3) := by
  constructor
  · intro i; fin_cases i <;> norm_num [three]
  · rintro ⟨e⟩
    have h := Fintype.card_le_of_injective e e.injective
    norm_num at h

def repeated : Fin 4 → Fin 3 := fun _ => 0
example : (∀ k, (1/3 : ℝ) ≤ three (repeated k)) ∧ ¬ Function.Injective repeated := by
  constructor
  · intro k; norm_num [three, repeated]
  · intro h
    have h01 := h (show repeated 0 = repeated 1 from rfl)
    norm_num at h01

example : (∀ i, 0 ≤ noMassNormalization i ∧ noMassNormalization i ≤ (1/2 : ℝ)) ∧
    (∑ i, noMassNormalization i) = 2 := by
  constructor
  · intro i; norm_num [noMassNormalization]
  · norm_num [noMassNormalization]

def firstFour : Fin 4 ↪ Fin 5 :=
  ⟨fun k => ⟨k.val, by omega⟩, by
    intro k l h
    apply Fin.ext
    exact congrArg (Fin.val : Fin 5 → ℕ) h⟩
example : (∑ i, negativeCoefficient i) = 1 ∧
    (∀ i, negativeCoefficient i ≤ (1/2 : ℝ)) ∧
    (∀ k, 0 ≤ negativeCoefficient (firstFour k)) ∧ negativeCoefficient 4 < 0 := by
  constructor
  · norm_num [negativeCoefficient, Fin.sum_univ_succ, cons_two, cons_three, cons_four]
  constructor
  · intro i; fin_cases i <;> norm_num [negativeCoefficient, cons_two, cons_three, cons_four]
  constructor
  · intro k; fin_cases k <;> change (0 : ℝ) ≤ (1/2 : ℝ) <;> norm_num
  · norm_num [negativeCoefficient, cons_four]

example : falseGap ∈ balancedPolytope ∧ (∀ k, (1/6 : ℝ) ≤ falseGap k) ∧
    ¬ (∀ i, falseGap i ≤ (1/2 : ℝ) - 1/6) := by
  constructor
  · constructor
    · intro i; fin_cases i <;> norm_num [falseGap, cons_two, cons_three]
    · norm_num [falseGap, Fin.sum_univ_succ, cons_two, cons_three]
  constructor
  · intro k; fin_cases k <;> norm_num [falseGap, cons_two, cons_three]
  · intro h; have h0 := h 0; norm_num [falseGap] at h0

example : falseFourthLowerBound ∈ balancedPolytope ∧
    (∀ i, falseFourthLowerBound i ≤ (1/2 : ℝ) - 1/6) ∧
    ¬ (∀ k, (1/3 : ℝ) ≤ falseFourthLowerBound k) := by
  constructor
  · constructor
    · intro i; fin_cases i <;> norm_num [falseFourthLowerBound, cons_two, cons_three]
    · norm_num [falseFourthLowerBound, Fin.sum_univ_succ, cons_two, cons_three]
  constructor
  · intro i; fin_cases i <;> norm_num [falseFourthLowerBound, cons_two, cons_three]
  · intro h; have h3 := h 3; norm_num [falseFourthLowerBound, cons_three] at h3

-- Strict refutations used by the six mathematical negative controls.
theorem refute_no_witness : ¬ (min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean three) := by
  norm_num [three_mean]
theorem refute_repeated_witness : ¬ (min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean three) :=
  refute_no_witness
theorem refute_no_normalization : ¬ (min ((0 : ℝ)/2) ((0 : ℝ)/4) ≤ 1/2 - mean noMassNormalization) := by
  norm_num [noMassNormalization_mean]
theorem refute_negative_coefficient : ¬ (min ((0 : ℝ)/2) ((0 : ℝ)/4) ≤ 1/2 - mean negativeCoefficient) := by
  norm_num [negativeCoefficient_mean]
theorem refute_false_gap : ¬ (min ((1/6 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean falseGap) := by
  norm_num [falseGap_mean]
theorem refute_false_fourth_bound : ¬ (min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean falseFourthLowerBound) := by
  norm_num [falseFourthLowerBound_mean]

example : min ((1/4 : ℝ)/2) ((1/4 : ℝ)/4) ≤
    1/2 - mean (fun _ : Fin 4 => (1/4 : ℝ)) := by
  have ha : (fun _ : Fin 4 => (1/4 : ℝ)) ∈ balancedPolytope := by
    constructor
    · intro i; constructor <;> norm_num
    · norm_num
  exact normalized_defect_lower_bound _ ha (1/4) (1/4)
    (by norm_num) (by norm_num) (Function.Embedding.refl _)
    (by intro k; norm_num) (by intro i; norm_num)

example : min ((0 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean three := by
  have ha : three ∈ balancedPolytope := by
    constructor
    · intro i; fin_cases i <;> norm_num [three]
    · norm_num [three, Fin.sum_univ_succ]
  exact normalized_defect_lower_bound_or_zero _ ha 0 (1/6)
    (by norm_num) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [three]) (Or.inl rfl)

end
end ExtensionAudit
