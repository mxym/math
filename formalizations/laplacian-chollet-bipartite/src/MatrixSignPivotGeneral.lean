import SignSwitchPivot
import PermanentDiagonalMinor
import Reindex

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Full all-index version of the permanent singleton-pivot bound for
an arbitrary finite real matrix diagonally sign-conjugate to a
nonnegative matrix. The distinguished vertex is no longer required
to be Option.none. -/
theorem permanent_pivot_of_signSwitch_nonnegative
    (A : Matrix n n ℝ) (v : n)
    (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (h_nonneg : ∀ i j, 0 ≤ signedSwitch A s i j) :
    A v v * Matrix.permanent (principalExcept A v) ≤
      Matrix.permanent A := by
  classical
  let β := {i : n // i ≠ v}
  let e : Option β ≃ n := Equiv.optionSubtypeNe v
  let M : Matrix (Option β) (Option β) ℝ :=
    fun i j => A (e i) (e j)
  let t : Option β → ℝ := fun i => s (e i)
  have ht : ∀ i, (t i)^2 = 1 := fun i => hs (e i)
  have hM : ∀ i j, 0 ≤ signedSwitch M t i j := by
    intro i j
    change 0 ≤ s (e i) * A (e i) (e j) * s (e j)
    exact h_nonneg (e i) (e j)
  have hroot : M none none = A v v := by
    change A (e none) (e none) = A v v
    rw [show e none = v from Equiv.optionSubtypeNe_none v]
  have hdel :
      Matrix.permanent (fun i j : β => M (some i) (some j)) =
        Matrix.permanent (principalExcept A v) := by
    rfl
  have hperm : Matrix.permanent M = Matrix.permanent A :=
    permanent_reindex_equiv A e
  have hp := permanent_optionPivot_of_signSwitch_nonnegative M t ht hM
  rw [hroot, hdel, hperm] at hp
  exact hp

end Chollet

#print axioms Chollet.permanent_pivot_of_signSwitch_nonnegative
