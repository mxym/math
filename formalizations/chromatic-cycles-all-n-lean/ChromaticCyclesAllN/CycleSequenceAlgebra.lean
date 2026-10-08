import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Cast

/-!
# The complete algebraic third-iterate obstruction for cycle polynomials

The polynomial coefficient sequence is expressed in terms of the first six
binomial coefficients, with the special zero and degree-one terms.  The
inequality is uniform in the cycle length.  A separate module must connect
this sequence with the actual chromatic polynomial of every cycle graph.
-/

namespace ChromaticCycleAll

def base (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => x - 1
  | 2 => x * (x - 1) / 2
  | 3 => x * (x - 1) * (x - 2) / 6
  | 4 => x * (x - 1) * (x - 2) * (x - 3) / 24
  | 5 => x * (x - 1) * (x - 2) * (x - 3) * (x - 4) / 120
  | _ => 0

def LC (a : ℕ → ℚ) (k : ℕ) : ℚ :=
  a k * a k - a (k - 1) * a (k + 1)

def quartic (x : ℚ) : ℚ :=
  2 * x^4 - 12 * x^3 - 327 * x^2 - 412 * x + 36

theorem quartic_shift (x : ℚ) :
    quartic x =
    2 * (x - 17)^4 + 124 * (x - 17)^3
      + 2529 * (x - 17)^2 + 17370 * (x - 17) + 6615 := by
  dsimp [quartic]
  ring

theorem quartic_positive (x : ℚ) (hx : 17 ≤ x) : 0 < quartic x := by
  rw [quartic_shift]
  have h : 0 ≤ x - 17 := by linarith
  positivity

theorem third_iterate_closed_formula (x : ℚ) :
    LC (LC (LC (base x))) 2 =
    -(x^3 * (x-1)^8 * (x+4) * quartic x) / 103680 := by
  simp only [LC, base]
  dsimp [quartic]
  ring

theorem third_iterate_strict_negative (x : ℚ) (hx : 17 ≤ x) :
    LC (LC (LC (base x))) 2 < 0 := by
  rw [third_iterate_closed_formula]
  have hn : 0 < x := by linarith
  have hm : 0 < x-1 := by linarith
  have hp : 0 < x+4 := by linarith
  have hq : 0 < quartic x := quartic_positive x hx
  have hprod : 0 < x^3 * (x-1)^8 * (x+4) * quartic x := by positivity
  have hneg : -(x^3 * (x-1)^8 * (x+4) * quartic x) < 0 := by linarith
  exact div_neg_of_neg_of_pos hneg (by norm_num)

theorem every_large_cycle_length_fails (n : ℕ) (hn : 17 ≤ n) :
    LC (LC (LC (base (n : ℚ)))) 2 < 0 :=
  third_iterate_strict_negative _ (by exact_mod_cast hn)


/-- The initial binomial coefficients of a cycle chromatic polynomial. -/
def binomialBase (n k : ℕ) : ℚ :=
  if k = 0 then 0 else if k = 1 then (n : ℚ) - 1
  else (Nat.choose n k : ℚ)

private theorem choose_cast_step (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n (k + 1) : ℚ) =
    (Nat.choose n k : ℚ) * ((n : ℚ) - k) / (k + 1 : ℚ) := by
  have h := Nat.choose_succ_right_eq n k
  have hh : (Nat.choose n (k+1) : ℚ) * ((k+1 : ℕ) : ℚ) =
      (Nat.choose n k : ℚ) * ((n-k : ℕ) : ℚ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hk] at hh
  apply (eq_div_iff (by positivity)).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem binomial_initial_agrees (n : ℕ) (hn : 17 ≤ n) (k : ℕ) (hk : k ≤ 5) :
    binomialBase n k = base (n : ℚ) k := by
  have h2 : (Nat.choose n 2 : ℚ) =
      (n : ℚ) * ((n : ℚ) - 1) / 2 :=
    Nat.cast_choose_two ℚ n
  have h3 : (Nat.choose n 3 : ℚ) =
      (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
    rw [show (3 : ℕ) = 2 + 1 by omega, choose_cast_step n 2 (by omega), h2]
    ring
  have h4 : (Nat.choose n 4 : ℚ) =
      (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
    rw [show (4 : ℕ) = 3 + 1 by omega, choose_cast_step n 3 (by omega), h3]
    ring
  have h5 : (Nat.choose n 5 : ℚ) =
      (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) *
        ((n : ℚ) - 3) * ((n : ℚ) - 4) / 120 := by
    rw [show (5 : ℕ) = 4 + 1 by omega, choose_cast_step n 4 (by omega), h4]
    ring
  have hs : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [binomialBase, base, h2, h3, h4, h5]

private theorem LC_agrees_below (a b : ℕ → ℚ) (N : ℕ)
    (h : ∀ i, i ≤ N + 1 → a i = b i) :
    ∀ i, i ≤ N → LC a i = LC b i := by
  intro i hi
  simp only [LC]
  rw [h i (by omega), h (i-1) (by omega), h (i+1) (by omega)]

theorem triple_LC_agrees (a b : ℕ → ℚ)
    (h : ∀ i, i ≤ 5 → a i = b i) :
    LC (LC (LC a)) 2 = LC (LC (LC b)) 2 := by
  have h1 := LC_agrees_below a b 4 (by simpa using h)
  have h2 := LC_agrees_below (LC a) (LC b) 3 (by simpa using h1)
  have h3 := LC_agrees_below (LC (LC a)) (LC (LC b)) 2 (by simpa using h2)
  exact h3 2 (by omega)

theorem all_large_cycle_binomial_sequences_fail (n : ℕ) (hn : 17 ≤ n) :
    LC (LC (LC (binomialBase n))) 2 < 0 := by
  rw [triple_LC_agrees (binomialBase n) (base (n : ℚ))
        (binomial_initial_agrees n hn)]
  exact every_large_cycle_length_fails n hn

end ChromaticCycleAll
