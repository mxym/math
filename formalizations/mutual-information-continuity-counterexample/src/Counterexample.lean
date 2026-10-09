import Mathlib

open scoped BigOperators
namespace MutualInformationCounterexample

noncomputable def eta (x : ℝ) : ℝ := -x * Real.log x
noncomputable def entropy {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, eta (p i)
noncomputable def jointEntropy (p : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, eta (p i j)
def marginalA (p : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ := ∑ j, p i j
def marginalB (p : Fin 3 → Fin 3 → ℝ) (j : Fin 3) : ℝ := ∑ i, p i j
noncomputable def mutualInformation (p : Fin 3 → Fin 3 → ℝ) : ℝ :=
  entropy (marginalA p) + entropy (marginalB p) - jointEntropy p
noncomputable def totalVariation (p q : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (∑ i, ∑ j, |p i j - q i j|) / 2
noncomputable def binaryEntropy (e : ℝ) : ℝ := eta e + eta (1-e)
noncomputable def P (e : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(1-e)/2, 0, 0], ![0, (1-e)/2, 0], ![0, 0, e]]
noncomputable def Q (e : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(1-e)/2, e/2, 0], ![e/2, (1-e)/2, 0], ![0, 0, 0]]
def IsProbability (p : Fin 3 → Fin 3 → ℝ) : Prop :=
  (∀ i j, 0 ≤ p i j) ∧ (∑ i, ∑ j, p i j) = 1

@[simp] theorem eta_zero : eta 0 = 0 := by simp [eta]
@[simp] theorem eta_one : eta 1 = 0 := by simp [eta]

theorem eta_half (x : ℝ) (hx : 0 < x) :
    2 * eta (x/2) = eta x + x * Real.log 2 := by
  unfold eta
  rw [Real.log_div (ne_of_gt hx) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem P_probability (e : ℝ) (he : 0 ≤ e) (h1 : e ≤ 1) :
    IsProbability (P e) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [P] <;> positivity
  · simp [P, Fin.sum_univ_succ]
    ring

theorem Q_probability (e : ℝ) (he : 0 ≤ e) (h1 : e ≤ 1) :
    IsProbability (Q e) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Q] <;> positivity
  · simp [Q, Fin.sum_univ_succ]
    ring

theorem P_marginalA (e : ℝ) : marginalA (P e) = ![(1-e)/2,(1-e)/2,e] := by
  funext i
  fin_cases i <;> simp [marginalA, P, Fin.sum_univ_succ]
theorem P_marginalB (e : ℝ) : marginalB (P e) = ![(1-e)/2,(1-e)/2,e] := by
  funext i
  fin_cases i <;> simp [marginalB, P, Fin.sum_univ_succ]
theorem Q_marginalA (e : ℝ) : marginalA (Q e) = ![(1:ℝ)/2,1/2,0] := by
  funext i
  fin_cases i <;> simp [marginalA, Q, Fin.sum_univ_succ] <;> ring
theorem Q_marginalB (e : ℝ) : marginalB (Q e) = ![(1:ℝ)/2,1/2,0] := by
  funext i
  fin_cases i <;> simp [marginalB, Q, Fin.sum_univ_succ] <;> ring

theorem mutualInformation_P (e : ℝ) (he : 0 < e) (h1 : e < 1) :
    mutualInformation (P e) = binaryEntropy e + (1-e)*Real.log 2 := by
  have ha := eta_half (1-e) (sub_pos.mpr h1)
  unfold mutualInformation
  rw [P_marginalA, P_marginalB]
  simp [entropy, jointEntropy, P, Fin.sum_univ_succ, binaryEntropy]
  nlinarith

theorem mutualInformation_Q (e : ℝ) (he : 0 < e) (h1 : e < 1) :
    mutualInformation (Q e) = Real.log 2 - binaryEntropy e := by
  have ha := eta_half (1-e) (sub_pos.mpr h1)
  have hb := eta_half e he
  have hc := eta_half 1 (by norm_num)
  simp only [eta_one, one_mul] at hc
  unfold mutualInformation
  rw [Q_marginalA, Q_marginalB]
  simp [entropy, jointEntropy, Q, Fin.sum_univ_succ, binaryEntropy]
  nlinarith

theorem totalVariation_P_Q (e : ℝ) (he : 0 ≤ e) :
    totalVariation (P e) (Q e) = e := by
  have hh : 0 ≤ e / 2 := by positivity
  simp [totalVariation, P, Q, Fin.sum_univ_succ, abs_neg,
    abs_of_nonneg he, abs_of_nonneg hh]
  ring

theorem log_sixteen : Real.log (16 : ℝ) = Real.log 8 + Real.log 2 := by
  rw [show (16 : ℝ) = 8 * 2 by norm_num,
    Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]

theorem binaryEntropy_gt (e : ℝ) (he : 0 < e) (h16 : e ≤ 1/16) :
    e * Real.log 16 < binaryEntropy e := by
  have h1 : e < 1 := by linarith
  have hlog : Real.log e ≤ -Real.log 16 := by
    have h := Real.log_le_log he h16
    simpa using h
  have hterm : e * Real.log 16 ≤ -e * Real.log e := by nlinarith
  have hnegative : Real.log (1-e) < 0 :=
    Real.log_neg (sub_pos.mpr h1) (by linarith)
  have hpositive : 0 < -(1-e) * Real.log (1-e) := by nlinarith
  unfold binaryEntropy eta
  linarith

theorem counterexample_family (e : ℝ) (he : 0 < e) (h16 : e ≤ 1/16) :
    IsProbability (P e) ∧ IsProbability (Q e) ∧
    totalVariation (P e) (Q e) = e ∧
    binaryEntropy e + e * Real.log 8 <
      |mutualInformation (P e) - mutualInformation (Q e)| := by
  have h1 : e < 1 := by linarith
  refine ⟨P_probability e he.le h1.le, Q_probability e he.le h1.le,
    totalVariation_P_Q e he.le, ?_⟩
  have hb := binaryEntropy_gt e he h16
  rw [log_sixteen] at hb
  have hstrict : binaryEntropy e + e * Real.log 8 <
      mutualInformation (P e) - mutualInformation (Q e) := by
    rw [mutualInformation_P e he h1, mutualInformation_Q e he h1]
    nlinarith
  exact lt_of_lt_of_le hstrict (le_abs_self _)

-- This is the actual universal classical-special-case claim, with
-- arbitrary joint probability tables, not an assumed entropy formula.
theorem proposed_classical_bound_false :
    ¬ (∀ (p q : Fin 3 → Fin 3 → ℝ) (e : ℝ),
      IsProbability p → IsProbability q → 0 < e → e ≤ 1/16 →
      totalVariation p q = e →
      |mutualInformation p - mutualInformation q| ≤
        binaryEntropy e + e * Real.log 8) := by
  intro h
  have hc := counterexample_family (1/32) (by norm_num) (by norm_num)
  exact (not_le_of_gt hc.2.2.2)
    (h (P (1/32)) (Q (1/32)) (1/32) hc.1 hc.2.1
      (by norm_num) (by norm_num) hc.2.2.1)

theorem counterexamples_arbitrarily_close (r : ℝ) (hr : 0 < r) :
    ∃ (p q : Fin 3 → Fin 3 → ℝ) (e : ℝ),
      IsProbability p ∧ IsProbability q ∧ 0 < e ∧ e < r ∧
      totalVariation p q = e ∧
      binaryEntropy e + e * Real.log 8 <
        |mutualInformation p - mutualInformation q| := by
  let e : ℝ := min (r / 2) (1 / 32)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have h16 : e ≤ 1 / 16 := by
    have h := min_le_right (r / 2) (1 / 32 : ℝ)
    dsimp [e]
    linarith
  have her : e < r := by
    have h := min_le_left (r / 2) (1 / 32 : ℝ)
    dsimp [e]
    linarith
  have hc := counterexample_family e he h16
  exact ⟨P e, Q e, e, hc.1, hc.2.1, he, her, hc.2.2.1, hc.2.2.2⟩

end MutualInformationCounterexample
