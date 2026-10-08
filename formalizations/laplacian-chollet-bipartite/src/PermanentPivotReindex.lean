import PermanentDiagonalMinor
import Reindex

namespace Chollet

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]

/-- Restriction of a type equivalence to the complements of the
distinguished indices. Both directions are explicitly inverses. -/
def exceptIndexEquiv (e : κ ≃ ι) (k : κ) :
    {x : κ // x ≠ k} ≃ {y : ι // y ≠ e k} where
  toFun := fun x =>
    ⟨e x.val, fun h => x.property (e.injective h)⟩
  invFun := fun y =>
    ⟨e.symm y.val, fun h => y.property (by
       calc
         y.val = e (e.symm y.val) := (e.apply_symm_apply y.val).symm
         _ = e k := by rw [h])⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv := by
    intro y
    apply Subtype.ext
    exact e.apply_symm_apply y.val

/-- The actual principal-submatrix permanent is invariant under a
simultaneous equivalence of the ambient index set, with the deleted
vertex moved to the corresponding index. -/
theorem permanent_principalExcept_reindex
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) (k : κ) :
    Matrix.permanent
      (principalExcept (fun i j : κ => A (e i) (e j)) k) =
    Matrix.permanent (principalExcept A (e k)) := by
  classical
  let d := exceptIndexEquiv e k
  have h :
      principalExcept (fun i j : κ => A (e i) (e j)) k =
      (fun i j : {x : κ // x ≠ k} =>
        (principalExcept A (e k)) (d i) (d j)) := by
    rfl
  rw [h]
  exact permanent_reindex_equiv (principalExcept A (e k)) d

/-- Permanent singleton-pivot inequalities transport by an arbitrary
finite equivalence of matrix index sets. -/
theorem permanent_rootPivot_reindex
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) (k : κ)
    (h : A (e k) (e k) * Matrix.permanent (principalExcept A (e k)) ≤
        Matrix.permanent A) :
    (fun i j : κ => A (e i) (e j)) k k *
      Matrix.permanent (principalExcept (fun i j : κ => A (e i) (e j)) k) ≤
      Matrix.permanent (fun i j : κ => A (e i) (e j)) := by
  rw [permanent_principalExcept_reindex, permanent_reindex_equiv]
  exact h

end Chollet

#print axioms Chollet.exceptIndexEquiv
#print axioms Chollet.permanent_principalExcept_reindex
#print axioms Chollet.permanent_rootPivot_reindex
