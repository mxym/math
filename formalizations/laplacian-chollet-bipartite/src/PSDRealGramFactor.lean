import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Ring

namespace Chollet

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectral_real_reconstruction (A : Matrix n n ℝ)
    (hA : A.PosSemidef) :
    A =
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal hA.isHermitian.eigenvalues *
        star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) := by
  simpa [Unitary.conjStarAlgAut_apply] using
    hA.isHermitian.spectral_theorem


/-- Spectral factorization of EVERY finite real positive semidefinite
matrix as a genuine real Gram array. Zero eigenvalues and singular
matrices are included. -/
theorem posSemidef_realGram_factor (A : Matrix n n ℝ)
    (hA : A.PosSemidef) :
    ∃ B : n → n → ℝ, ∀ i j : n,
      A i j = ∑ k : n, B k i * B k j := by
  let U : Matrix n n ℝ :=
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let eig : n → ℝ := hA.isHermitian.eigenvalues
  let B : n → n → ℝ :=
    fun k i => Real.sqrt (eig k) * U i k
  have heig (k : n) : 0 ≤ eig k :=
    hA.eigenvalues_nonneg k
  have hspec : A = U * Matrix.diagonal eig * star U := by
    exact spectral_real_reconstruction A hA
  refine ⟨B, ?_⟩
  intro i j
  rw [hspec]
  change (U * Matrix.diagonal eig * star U) i j =
    ∑ k : n, (Real.sqrt (eig k) * U i k) *
      (Real.sqrt (eig k) * U j k)
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [star_trivial]
  have hsq : Real.sqrt (eig k) * Real.sqrt (eig k) = eig k := by
    nlinarith [Real.sq_sqrt (heig k)]
  calc
    U i k * eig k * U j k =
      (Real.sqrt (eig k) * Real.sqrt (eig k)) *
        (U i k * U j k) := by rw [hsq]; ring
    _ = (Real.sqrt (eig k) * U i k) *
          (Real.sqrt (eig k) * U j k) := by ring

#print axioms Chollet.posSemidef_realGram_factor

end Chollet
