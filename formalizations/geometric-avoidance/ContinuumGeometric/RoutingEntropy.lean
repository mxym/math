import ContinuumGeometric.RoutingChoices
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Scalar entropy estimates for the proved boundary-complete local signatures.
The candidate count and local-window lower bound are explicit premises, to be
discharged by the actual tree construction. The additive +1 keeps the estimate
valid even for an empty candidate family.
-/
namespace ContinuumGeometric

theorem fair_selector_terminal_miss_exp_bound (p : ℝ) (hp : 0 ≤ p)
    (hp₁ : p ≤ 1) (m : ℕ) :
    (1 - p / 2) ^ m ≤ Real.exp (-p * (m : ℝ) / 2) := by
  have hb : 0 ≤ 1 - p / 2 := by linarith
  have h := pow_le_pow_left₀ hb (Real.one_sub_le_exp_neg (p / 2)) m
  calc
    _ ≤ Real.exp ((m : ℝ) * (-p / 2)) := by
      simpa only [neg_div, Real.exp_nat_mul] using h
    _ = Real.exp (-p * (m : ℝ) / 2) := by congr 1; ring

theorem fair_selector_terminal_miss_window_bound (p η : ℝ) (hp : 0 ≤ p)
    (hp₁ : p ≤ 1) (M m ell : ℕ)
    (hm : η * ((M : ℝ) - 1) * (ell : ℝ) ≤ (m : ℝ)) :
    (1 - p / 2) ^ m ≤
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * (ell : ℝ)) := by
  apply (fair_selector_terminal_miss_exp_bound p hp hp₁ m).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hm hp
  nlinarith

theorem signature_entropy_exp_bound (P ell : ℕ) :
    20 * ((P : ℝ) * (3 + (2 : ℝ) ^ (2 * ell + 3)) + 5) ^ 2 ≤
      5120 * ((P : ℝ) + 1) ^ 2 * Real.exp (4 * Real.log 2 * (ell : ℝ)) := by
  let Q : ℝ := (2 : ℝ) ^ (2 * ell)
  have hQ : 1 ≤ Q := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hP : 0 ≤ (P : ℝ) := Nat.cast_nonneg _
  have hpower : (2 : ℝ) ^ (2 * ell + 3) = 8 * Q := by
    norm_num [Q, pow_add, mul_comm]
  have hinside : (P : ℝ) * (3 + 8 * Q) + 5 ≤ 16 * ((P : ℝ) + 1) * Q := by
    nlinarith
  have hsquare := pow_le_pow_left₀ (by positivity :
    0 ≤ (P : ℝ) * (3 + 8 * Q) + 5) hinside 2
  have hexp : Real.exp (4 * Real.log 2 * (ell : ℝ)) = Q ^ 2 := by
    calc
      _ = Real.exp (((4 * ell : ℕ) : ℝ) * Real.log 2) := by congr 1; push_cast; ring
      _ = (2 : ℝ) ^ (4 * ell) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ = Q ^ 2 := by dsimp [Q]; rw [← pow_mul]; congr 1; omega
  rw [hpower, hexp]
  nlinarith

theorem signature_entropy_decay_bound (P ell : ℕ) (lam : ℝ) :
    (20 * ((P : ℝ) * (3 + (2 : ℝ) ^ (2 * ell + 3)) + 5) ^ 2) *
      Real.exp (-lam * (ell : ℝ)) ≤
    5120 * ((P : ℝ) + 1) ^ 2 *
      Real.exp (-(lam - 4 * Real.log 2) * (ell : ℝ)) := by
  have h := mul_le_mul_of_nonneg_right (signature_entropy_exp_bound P ell)
    (Real.exp_nonneg (-lam * (ell : ℝ)))
  calc
    _ ≤ 5120 * ((P : ℝ) + 1) ^ 2 * Real.exp (4 * Real.log 2 * (ell : ℝ)) *
        Real.exp (-lam * (ell : ℝ)) := h
    _ = (5120 * ((P : ℝ) + 1) ^ 2) *
        (Real.exp (4 * Real.log 2 * (ell : ℝ)) * Real.exp (-lam * (ell : ℝ))) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- The position factor is retained until U is chosen by the logarithmic schedule. -/
theorem signature_entropy_position_bound (M P U T ell L : ℕ) (k lam : ℝ)
    (hM : 1 ≤ M) (hT : T ≤ U) (hk : |k| ≤ U)
    (hP : (P : ℝ) ≤ (M : ℝ) * ((U : ℝ) + T + |k| + 2))
    (hL : L ≤ ell) (hκ : 0 < lam - 4 * Real.log 2) :
    (20 * ((P : ℝ) * (3 + (2 : ℝ) ^ (2 * ell + 3)) + 5) ^ 2) *
      Real.exp (-lam * (ell : ℝ)) ≤
    46080 * (M : ℝ) ^ 2 * ((U : ℝ) + 1) ^ 2 *
      Real.exp (-(lam - 4 * Real.log 2) * (L : ℝ)) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hTr : (T : ℝ) ≤ U := by exact_mod_cast hT
  have hUr : 0 ≤ (U : ℝ) := Nat.cast_nonneg _
  have hPr : 0 ≤ (P : ℝ) := Nat.cast_nonneg _
  have hpos : (P : ℝ) + 1 ≤ 3 * (M : ℝ) * ((U : ℝ) + 1) := by
    nlinarith
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (P : ℝ) + 1) hpos 2
  have hcoeff : 5120 * ((P : ℝ) + 1) ^ 2 ≤
      46080 * (M : ℝ) ^ 2 * ((U : ℝ) + 1) ^ 2 := by
    nlinarith
  have hLr : (L : ℝ) ≤ ell := by exact_mod_cast hL
  have hdecay : Real.exp (-(lam - 4 * Real.log 2) * (ell : ℝ)) ≤
      Real.exp (-(lam - 4 * Real.log 2) * (L : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact (signature_entropy_decay_bound P ell lam).trans
    (mul_le_mul hcoeff hdecay (Real.exp_nonneg _) (by positivity))

end ContinuumGeometric
