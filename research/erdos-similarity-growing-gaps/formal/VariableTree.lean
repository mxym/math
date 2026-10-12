import Mathlib.Tactic

/-! Uniform algebra used in Lemmas 6–7 of the accompanying paper.
This file does NOT formalize the new analytic avoidance theorem.
The index is zero at the empty tree; positive indices are tree heights. -/
namespace GrowingGap

def span (b g L : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => b * L + (b - 1) * g
  | n + 2 => 2 * b * span b g L (n + 1) + (3 * b - 1) * g

theorem uniform_span (b g L : ℝ) (hb : 2 ≤ b) (hg : 0 ≤ g)
    (n : ℕ) : span b g L (n + 1) + 2 * g ≤ b * (2 * b) ^ n * (L + 2 * g) := by
  induction n with
  | zero =>
    simp only [span, pow_zero, mul_one]
    nlinarith
  | succ n ih =>
    have hb0 : 0 ≤ 2 * b := by linarith
    have h := mul_le_mul_of_nonneg_left ih hb0
    simp only [span, pow_succ]
    nlinarith

theorem span_bound (b g L : ℝ) (hb : 2 ≤ b) (hg : 0 ≤ g)
    (hL : 0 ≤ L) (n : ℕ) : span b g L (n + 1) ≤ (2 * b) ^ (n + 1) * (L + 2 * g) := by
  have h := uniform_span b g L hb hg n
  have hp : 0 ≤ (2 * b) ^ n := pow_nonneg (by linarith) _
  have hl : 0 ≤ L + 2 * g := by linarith
  have hprod : 0 ≤ b * (2 * b) ^ n * (L + 2 * g) :=
    mul_nonneg (mul_nonneg (by linarith) hp) hl
  simp only [pow_succ]
  nlinarith

def edges (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => b + b * edges b n

theorem edges_identity (b : ℝ) (n : ℕ) :
    edges b n * (b - 1) = b ^ (n + 1) - b := by
  induction n with
  | zero => simp [edges]
  | succ n ih =>
    have h := congrArg (fun x : ℝ => b * x) ih
    simp only [pow_succ] at h
    simp only [edges, pow_succ]
    nlinarith

theorem edges_bound (b : ℝ) (hb : 2 ≤ b) (n : ℕ) :
    edges b n ≤ 2 * b ^ n := by
  have hb0 : 0 ≤ b := by linarith
  have hpos : 0 ≤ edges b n := by
    induction n with
    | zero => simp [edges]
    | succ n ih =>
      have h := add_nonneg hb0 (mul_nonneg hb0 ih)
      simpa only [edges] using h
  have hid := edges_identity b n
  have hp : 0 ≤ b ^ n := pow_nonneg (by linarith) _
  have hmul : 0 ≤ (b - 2) * b ^ n := mul_nonneg (by linarith) hp
  simp only [pow_succ] at hid
  nlinarith

-- Boundary and genuinely false stronger-bound controls.
example : span 2 1 0 1 = 1 := by norm_num [span]
example : ¬ span 2 1 0 1 ≤ 0 := by norm_num [span]
example : edges 2 3 = 14 := by norm_num [edges]

#print axioms uniform_span
#print axioms span_bound
#print axioms edges_identity
#print axioms edges_bound
end GrowingGap
