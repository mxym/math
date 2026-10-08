import QDefinitions
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.BigOperators

open scoped BigOperators
namespace Bapat
 theorem star_permutationWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (σ : Equiv.Perm (Fin n)) :
    star (permutationWeight A σ) = permutationWeight A σ.symm := by
  unfold permutationWeight
  rw [star_prod]
  simp only [hA.apply]
  simpa using Equiv.prod_comp σ (fun r => A r (σ.symm r))

/-- The actual q-permanent is real on the real axis for a Hermitian matrix. -/
 theorem star_qPermanent_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) : star (qPermanent A (q : ℂ)) = qPermanent A (q : ℂ) := by
  unfold qPermanent
  rw [star_sum]
  simp only [star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
  simp_rw [← Complex.star_def, star_permutationWeight A hA]
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        (q : ℂ) ^ inversionCount σ.symm * permutationWeight A σ.symm := by
      simp_rw [inversionCount_inverse]
      simp only [mul_comm]
    _ = _ := by
      let E : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
        ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
      exact Equiv.sum_comp E (fun σ =>
        (q : ℂ) ^ inversionCount σ * permutationWeight A σ)

end Bapat
