import HydrologyTree.CompartmentMatrix
import HydrologyTree.LeadingCoefficients
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Actual characteristic/cofactor coefficient semantics and the root inverse
entry. Inverses are totalized at poles; true two-sided inverses are asserted
only under a checked nonzero determinant hypothesis. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma scalar_sub_principal {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (s : ℝ) :
    (Matrix.scalar (Fin (n+1)) s - A).submatrix Fin.succ Fin.succ =
      Matrix.scalar (Fin n) s - A.submatrix Fin.succ Fin.succ := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- Exact cofactor identity for the root entry of the adjugate. -/
lemma root_adjugate_eq_principal_det {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    A.adjugate 0 0 = (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp

/-- The actual root inverse entry equals the unreduced characteristic/cofactor
ratio. This algebraic identity uses the library's totalized inverse at poles. -/
theorem root_inverse_entry_eq {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (s : ℝ) :
    (Matrix.scalar (Fin (n+1)) s - A)⁻¹ 0 0 =
      (A.submatrix Fin.succ Fin.succ).charpoly.eval s / A.charpoly.eval s := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [root_adjugate_eq_principal_det, scalar_sub_principal,
    ← Matrix.eval_charpoly, ← Matrix.eval_charpoly]
  ring

/-- Outside the characteristic roots, this is a true two-sided matrix inverse. -/
theorem root_resolvent_is_inverse {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (s : ℝ) (hs : A.charpoly.eval s ≠ 0) :
    (Matrix.scalar (Fin (n+1)) s - A)⁻¹ * (Matrix.scalar (Fin (n+1)) s - A) = 1 ∧
    (Matrix.scalar (Fin (n+1)) s - A) * (Matrix.scalar (Fin (n+1)) s - A)⁻¹ = 1 := by
  have hd : IsUnit (Matrix.scalar (Fin (n+1)) s - A).det := by
    rw [← Matrix.eval_charpoly, isUnit_iff_ne_zero]
    exact hs
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

/-- Root-resolvent entry of the actual conservative tree generator. -/
def physicalRootResponse {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (s : ℝ) : ℝ :=
  (Matrix.scalar (Fin (n+1)) s - compartmentMatrix t x)⁻¹ 0 0

theorem physicalRootResponse_eq {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (s : ℝ) :
    physicalRootResponse t x s =
      (physicalRootCofactor t x).eval s / (physicalCharacteristic t x).eval s :=
  root_inverse_entry_eq _ _

/-- The target coefficient map reads actual matrix characteristic polynomials.
Its all-tree Jacobian factorization is not assumed or declared here. -/
def physicalCoefficientMap {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    Coeff (n+1) × Coeff n :=
  (cut (n+1) (physicalCharacteristic t x), cut n (physicalRootCofactor t x))

lemma physicalCharacteristic_monic {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).Monic := Matrix.charpoly_monic _

lemma physicalCharacteristic_natDegree {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).natDegree = n+1 := by
  simp [physicalCharacteristic]

lemma physicalRootCofactor_monic {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalRootCofactor t x).Monic := Matrix.charpoly_monic _

lemma physicalRootCofactor_natDegree {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalRootCofactor t x).natDegree = n := by
  simp [physicalRootCofactor]

/-- The output coefficients encode the entire actual characteristic polynomial. -/
theorem physicalCoefficientMap_first_reconstruct {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (monicPoly (physicalCoefficientMap t x).1 : ℝ[X]) = physicalCharacteristic t x :=
  monic_reconstruct _ (physicalCharacteristic_monic t x) (physicalCharacteristic_natDegree t x)

/-- The second output encodes the actual root cofactor, with boundary diagonals retained. -/
theorem physicalCoefficientMap_second_reconstruct {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (monicPoly (physicalCoefficientMap t x).2 : ℝ[X]) = physicalRootCofactor t x :=
  monic_reconstruct _ (physicalRootCofactor_monic t x) (physicalRootCofactor_natDegree t x)

end HydrologyTree
