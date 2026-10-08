import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Chollet

/-- Monomer-dimer partition function for a path with each monomer weighted d
and each dimer weighted 1. Computed entirely by a two-term Nat recurrence. -/
def pathMatchingWeight (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => d
  | n + 2 => d * pathMatchingWeight d (n + 1) + pathMatchingWeight d n

/-- For n>=3, the matching partition function for an n-cycle is
P_n(d) + P_(n-2)(d). -/
def cycleMatchingWeight (d n : ℕ) : ℕ :=
  pathMatchingWeight d n + pathMatchingWeight d (n - 2)

private theorem pathDouble_recurrence (n : ℕ) :
    2^(n+2) * pathMatchingWeight 2 (n+2) =
      4 * (2^(n+1) * pathMatchingWeight 2 (n+1)) +
      4 * (2^n * pathMatchingWeight 2 n) := by
  simp only [pathMatchingWeight, pow_succ]
  ring

private theorem pathFour_recurrence (n : ℕ) :
    pathMatchingWeight 4 (n+2) =
      4 * pathMatchingWeight 4 (n+1) + pathMatchingWeight 4 n := by
  rfl

/-- The two-scaled path weight dominates the four-weight path value
in every length, including zero and one. -/
theorem pathMatchingWeight_le_scaled (n : ℕ) :
    pathMatchingWeight 4 n ≤
      2^n * pathMatchingWeight 2 n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    decide
  | one =>
    decide
  | more n ih ih1 =>
    rw [pathDouble_recurrence, pathFour_recurrence]
    omega


/-- Uniform strict gap for path matching partition functions. Unlike the
original logarithmic/PSD permanent proof, this is elementary arithmetic
in the natural numbers and valid for every n>=3. -/
theorem pathMatchingWeight_strict_gap (n : ℕ) :
    pathMatchingWeight 4 (n+3) + 2^(n+4) + 2 ≤
      2^(n+3) * pathMatchingWeight 2 (n+3) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    decide
  | one =>
    decide
  | more n ih ih1 =>
    have hd : 2^(n+5) * pathMatchingWeight 2 (n+5) =
        4*(2^(n+4)*pathMatchingWeight 2 (n+4)) +
        4*(2^(n+3)*pathMatchingWeight 2 (n+3)) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        pathDouble_recurrence (n+3)
    have hf : pathMatchingWeight 4 (n+5) =
        4*pathMatchingWeight 4 (n+4) +
          pathMatchingWeight 4 (n+3) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        pathFour_recurrence (n+3)
    have hpow : 2^(n+6) = 2 * 2^(n+5) := by
      rw [show n+6 = (n+5)+1 by omega, pow_succ]
      omega
    have hnonneg := pathMatchingWeight_le_scaled (n+3)
    simp only [Nat.add_assoc, Nat.reduceAdd] at ih1 ⊢
    omega

/-- A cycle has the path monomer-dimer partition function plus the
contribution of matchings crossing the closing edge. Here the definition
is valid in all natural dimensions, but the theorem uses n>=3. -/
theorem cycleMatchingWeight_strict_gap (n : ℕ) :
    cycleMatchingWeight 4 (n+3) + 2^(n+4) + 2 ≤
      2^(n+3) * cycleMatchingWeight 2 (n+3) := by
  have hm := pathMatchingWeight_strict_gap n
  have hn := pathMatchingWeight_le_scaled (n+1)
  have hp : 2^(n+3) = 4*2^(n+1) := by
    rw [show n+3=(n+1)+2 by omega, pow_add]
    norm_num
    ring
  unfold cycleMatchingWeight
  simp only [show (n+3)-2=n+1 by omega]
  rw [mul_add]
  have hpow1 : 2^(n+3) * pathMatchingWeight 2 (n+1) =
      4*(2^(n+1)*pathMatchingWeight 2 (n+1)) := by
    rw [hp]
    ring
  rw [hpow1]
  omega

end Chollet

#print axioms Chollet.pathMatchingWeight_le_scaled
#print axioms Chollet.pathMatchingWeight_strict_gap
#print axioms Chollet.cycleMatchingWeight_strict_gap
