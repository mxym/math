import HydrologyTree.CatenaryCanonical
import HydrologyTree.CoordinateEnergy

/-! Standard-coordinate, all-rate endpoint-catenary formula. The factor is
proved to be a fixed sign, not an unspecified nonzero normalization constant. -/
open Polynomial Module Matrix
noncomputable section
namespace HydrologyTree

lemma arrayInput_basisDot (n : ℕ) (x y : TreeRates n) :
    basisDot (catenaryArrayInputBasis n) x y = physicalRateDot n x y := by
  simp [basisDot, catenaryArrayInputBasis, physicalRateDot]

lemma arrayOutput_basisDot (n : ℕ) (p q : PathCoefficients n) :
    basisDot (catenaryArrayOutputBasis n) p q = pathCoefficientDot n p q := by
  simp [basisDot, catenaryArrayOutputBasis, pathCoefficientDot, coefficientDot,
    Polynomial.degreeLT.basis_repr]

/-- The two actual coordinate rearrangements are unscaled; no numerical determinant
or finite-dimensional sample is used to certify the normalization. -/
theorem catenaryCoordinateDet_sq (n : ℕ) : catenaryCoordinateDet n ^ 2 = 1 := by
  apply det_sq_of_basisDot_preserved (catenaryArrayOutputBasis n) (catenaryArrayInputBasis n)
  intro p q
  rw [arrayInput_basisDot, arrayOutput_basisDot]
  change physicalRateDot n (pathRateEquiv n (pathCoefficientEquiv n p))
    (pathRateEquiv n (pathCoefficientEquiv n q)) = pathCoefficientDot n p q
  rw [pathRateEquiv_dot, pathCoefficientEquiv_dot]

/-- The standard-coordinate normalization constant has magnitude exactly one. -/
theorem catenaryCanonicalFactor_sq (n : ℕ) : catenaryCanonicalFactor n ^ 2 = 1 := by
  rw [catenaryCanonicalFactor, div_pow, pathOrientation_sq, catenaryCoordinateDet_sq]
  norm_num

lemma real_sq_one_sign (c : ℝ) (hc : c^2 = 1) : c = 1 ∨ c = -1 := by
  have h : (c-1)*(c+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

/-- A sign independent of every rate vector, for every number n+1 of compartments.
This is the actual physical coefficient-map determinant in standard ascending
P/F coefficient and physical-array bases, including all zero-rate boundaries. -/
theorem catenary_standard_jacobian (n : ℕ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x : TreeRates n,
      catenaryCanonicalJacobian n x = ε *
        ∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1) := by
  exact ⟨catenaryCanonicalFactor n,
    real_sq_one_sign _ (catenaryCanonicalFactor_sq n), catenaryCanonicalJacobian_eq n⟩

/-- Orientation-free exact polynomial identity for the actual canonical Jacobian. -/
theorem catenary_standard_jacobian_sq (n : ℕ) (x : TreeRates n) :
    catenaryCanonicalJacobian n x ^ 2 =
      (∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1)) ^ 2 := by
  rw [catenaryCanonicalJacobian_eq, mul_pow, catenaryCanonicalFactor_sq, one_mul]

/-- Exact singular locus in standard physical and polynomial coordinates. -/
theorem catenary_standard_singular_locus (n : ℕ) (x : TreeRates n) :
    catenaryCanonicalJacobian n x = 0 ↔
      (∃ i : Fin n, x.1 i.succ = 0) ∨
      (∃ i : Fin n, i.val+1 < n ∧ x.2 i = 0) :=
  catenaryCanonicalJacobian_zero_iff n x

end HydrologyTree
