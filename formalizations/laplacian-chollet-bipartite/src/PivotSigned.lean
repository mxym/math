import PivotNonnegative
import Signed
import Mathlib.Tactic.Ring

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact invariance of the genuine matrix permanent under diagonal
±1 congruence, proved by reindexing all permutation monomials. -/
theorem permanent_signedSwitch_eq (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1) :
    Matrix.permanent (signedSwitch A s) = Matrix.permanent A := by
  classical
  have hsp : (∏ i, s i)^2 = 1 := by
    rw [← Finset.prod_pow]
    simp only [hs]
    simp
  simp only [Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  have hp : (∏ i, s (σ i)) = ∏ i, s i :=
    Equiv.prod_comp σ s
  calc
    (∏ i, signedSwitch A s (σ i) i) =
      (∏ i, s (σ i)) * (∏ i, A (σ i) i) * (∏ i, s i) := by
        simp only [signedSwitch, Finset.prod_mul_distrib, mul_assoc]
    _ = (∏ i, A (σ i) i) * ((∏ i, s i)^2) := by rw [hp]; ring
    _ = (∏ i, A (σ i) i) := by rw [hsp]; ring

/-- Root singleton-permanent lower bound for all matrices that can be
diagonally sign-switched to entrywise nonnegative, arbitrary finite order.
No PSD or Lieb theorem invoked. -/
theorem permanent_root_pivot_of_signed_nonnegative
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix (Option α) (Option α) ℝ)
    (s : Option α → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (hn : ∀ i j, 0 ≤ signedSwitch A s i j) :
    A none none *
      Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
      Matrix.permanent A := by
  let B := signedSwitch A s
  have hdiag : B none none = A none none := by
    dsimp [B, signedSwitch]
    calc
      s none * A none none * s none =
        (s none)^2 * A none none := by ring
      _ = _ := by rw [hs none]; ring
  have hminor :
      (fun i j : α => B (some i) (some j)) =
        signedSwitch (fun i j : α => A (some i) (some j))
          (fun i => s (some i)) := rfl
  have hminorPer :
      Matrix.permanent (fun i j : α => B (some i) (some j)) =
        Matrix.permanent (fun i j : α => A (some i) (some j)) := by
    rw [hminor]
    exact permanent_signedSwitch_eq _ _ (fun i => hs (some i))
  have hper :
      Matrix.permanent B = Matrix.permanent A :=
    permanent_signedSwitch_eq A s hs
  have hroot := permanent_root_pivot_of_nonnegative B hn
  rw [hdiag, hminorPer, hper] at hroot
  exact hroot

end Chollet

#print axioms Chollet.permanent_signedSwitch_eq
#print axioms Chollet.permanent_root_pivot_of_signed_nonnegative
