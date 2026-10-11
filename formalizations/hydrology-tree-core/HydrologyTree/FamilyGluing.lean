import HydrologyTree.FamilyResultants
import HydrologyTree.FamilySmoothness
import HydrologyTree.TangentJacobian

/-! The all-arity polynomial gluing theorem in actual coefficient spaces.
All derivatives, smoothness and polynomial identities are proved; there is no
coprimality, positivity or nonsingularity hypothesis. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

/-- Actual numerator sum, one numerator in place of each corresponding factor. -/
def familyNumerator : (ms : List ℕ) → ProductInput ms → ProductInput ms → ℝ[X]
  | [], _, _ => 0
  | _ :: ms, p, r =>
      (r.1 : ℝ[X]) * (monicPoly (familyProduct ms p.2) : ℝ[X]) +
      (monicPoly p.1 : ℝ[X]) * familyNumerator ms p.2 r.2

lemma monoSylv_polynomial {m n : ℕ} (p r : PolyPair m n) :
    (monoSylv p r : ℝ[X]) =
      (monicPoly p.1 : ℝ[X]) * (r.2 : ℝ[X]) +
      (monicPoly p.2 : ℝ[X]) * (r.1 : ℝ[X]) := rfl

/-- The derivative applied to the numerator data is exactly the full numerator
polynomial, not merely a sampled evaluation or a truncated approximation. -/
theorem familyProductDerivative_polynomial (ms : List ℕ)
    (p r : ProductInput ms) :
    (familyProductDerivative ms p r : ℝ[X]) = familyNumerator ms p r := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change (monoSylv (p.1,familyProduct ms p.2)
      (r.1,familyProductDerivative ms p.2 r.2) : ℝ[X]) = _
    rw [monoSylv_polynomial, ih]
    dsimp only [familyNumerator]
    ring

/-- Arbitrarily many monic factors with their arbitrary strict-degree numerators. -/
def familyGlue (ms : List ℕ) (x : ProductInput ms × ProductInput ms) :
    Coeff ms.sum × Coeff ms.sum :=
  (familyProduct ms x.1, cut ms.sum (familyNumerator ms x.1 x.2))

lemma familyGlue_eq_tangentLift (ms : List ℕ) :
    familyGlue ms = tangentLift (familyProduct ms) (familyProductDerivative ms) := by
  funext x
  apply Prod.ext
  · rfl
  · change cut ms.sum (familyNumerator ms x.1 x.2) = familyProductDerivative ms x.1 x.2
    rw [← familyProductDerivative_polynomial, cut_coe]

/-- The full second output encodes the true numerator polynomial. -/
theorem familyGlue_numerator_exact (ms : List ℕ) (x : ProductInput ms × ProductInput ms) :
    ((familyGlue ms x).2 : ℝ[X]) = familyNumerator ms x.1 x.2 := by
  rw [familyGlue_eq_tangentLift]
  exact familyProductDerivative_polynomial ms x.1 x.2

theorem hasFDerivAt_familyGlue (ms : List ℕ) (x : ProductInput ms × ProductInput ms) :
    HasFDerivAt (familyGlue ms) (tangentDerivative (familyProductDerivative ms) x) x := by
  rw [familyGlue_eq_tangentLift]
  exact hasFDerivAt_tangentLift _ _ _ (hasFDerivAt_familyProduct ms x.1)
    (differentiable_familyProductDerivative ms x.1)

def familyGlueJacobian (ms : List ℕ) (x : ProductInput ms × ProductInput ms) : ℝ :=
  (LinearMap.toMatrix ((familyBasis ms).prod (familyBasis ms))
    ((degreeLT.basis ℝ ms.sum).prod (degreeLT.basis ℝ ms.sum))
    (fderiv ℝ (familyGlue ms) x).toLinearMap).det

/-- The full gluing Jacobian, for every finite factor family and all coefficients,
is the square of the pairwise resultant product, including every singular case. -/
theorem familyGlueJacobian_eq_pairwise (ms : List ℕ) (x : ProductInput ms × ProductInput ms) :
    familyGlueJacobian ms x = pairwiseResultants (familyPolynomials ms x.1)^2 := by
  rw [familyGlueJacobian, familyGlue_eq_tangentLift,
    tangentLift_jacobian _ _ _ _ _ (hasFDerivAt_familyProduct ms x.1)
      (differentiable_familyProductDerivative ms x.1),
    det_familyProductDerivative, familyResultant_eq_pairwise]

end HydrologyTree
