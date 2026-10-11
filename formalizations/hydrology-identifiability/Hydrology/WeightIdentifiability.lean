import Hydrology.Generic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace HydrologyIdentifiability

open scoped BigOperators

noncomputable section

/-- For pairwise distinct rates, the first `k` exact moments uniquely recover
all output weights when the rates themselves are known. This is the Vandermonde
step in finite-spectrum identification. -/
theorem finiteMoment_weights_unique {k : ℕ} (w v l : Fin k → ℝ)
    (hinj : Function.Injective l)
    (hmom : ∀ j : Fin k,
      finiteMoment w l (j : ℕ) = finiteMoment v l (j : ℕ)) :
    w = v := by
  have hz : w - v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro j
    have h : finiteMoment w l (j : ℕ) - finiteMoment v l (j : ℕ) = 0 :=
      sub_eq_zero.mpr (hmom j)
    dsimp [finiteMoment] at h ⊢
    simp only [Finset.sum_sub_distrib, sub_mul] at h ⊢
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  funext i
  have hi := congrFun hz i
  exact sub_eq_zero.mp hi

end
end HydrologyIdentifiability
