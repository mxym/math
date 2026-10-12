import HydrologyTree.SymmetricGenerator
import Mathlib.Analysis.Matrix.PosDef

/-! Strictly negative real characteristic roots for the actual positive physical
tree generator. Spectrum and positivity are derived from the constructed energy
form and the library spectral theorem, not assumed as a stability hypothesis. -/
open Matrix Polynomial Unitary
noncomputable section
namespace HydrologyTree

lemma charpoly_neg_posDef {I : Type*} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℝ) (hB : B.PosDef) :
    (-B).charpoly = ∏ i : I, (X + C (hB.isHermitian.eigenvalues i)) := by
  have hn : -B = conjStarAlgAut ℝ _ hB.isHermitian.eigenvectorUnitary
      (-Matrix.diagonal (RCLike.ofReal ∘ hB.isHermitian.eigenvalues)) := by
    rw [map_neg, ← hB.isHermitian.spectral_theorem]
  rw [hn, conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
  simp [Matrix.diagonal_neg, Matrix.charpoly_diagonal, Function.comp_def]

/-- Complete factorization into strictly negative real modes, with algebraic
multiplicity retained. No simplicity or absence of cancellations is claimed. -/
theorem physical_characteristic_negative_real_factorization {n : ℕ}
    (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (hf : ∀ e : Fin n, 0 < x.2 e) :
    ∃ r : Fin (n+1) → ℝ, (∀ i, 0 < r i) ∧
      physicalCharacteristic t x = ∏ i : Fin (n+1), (X + C (r i)) := by
  have hB := symmetricNegativeGenerator_posDef t x hell ha hf
  refine ⟨hB.isHermitian.eigenvalues, fun i => hB.eigenvalues_pos i, ?_⟩
  rw [physical_charpoly_symmetric t x ha hf]
  exact charpoly_neg_posDef _ hB

/-- In particular the actual resolvent has no nonnegative real poles. -/
theorem physical_characteristic_pos_on_nonnegative {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (hf : ∀ e : Fin n, 0 < x.2 e) (s : ℝ) (hs : 0 ≤ s) :
    0 < (physicalCharacteristic t x).eval s := by
  obtain ⟨r,hr,hP⟩ := physical_characteristic_negative_real_factorization t x hell ha hf
  rw [hP, Polynomial.eval_prod]
  apply Finset.prod_pos
  intro i _
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact add_pos_of_nonneg_of_pos hs (hr i)

end HydrologyTree
