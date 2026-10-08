import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic

namespace Chollet

/-- Simultaneously reindexing both indices of a real matrix through any
equivalence leaves the actual matrix permanent unchanged. -/
theorem permanent_reindex_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    Matrix.permanent (fun i j : κ => A (e i) (e j)) =
      Matrix.permanent A := by
  classical
  unfold Matrix.permanent
  apply Fintype.sum_equiv (e.permCongr)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.permCongr_apply]

end Chollet

#print axioms Chollet.permanent_reindex_equiv
