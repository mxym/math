import HydrologyTree.Gluing
import HydrologyTree.LeadingCoefficients

/-! Multiplication of actual monic coefficient vectors. This supplies the
one-copy Sylvester derivative needed in the arbitrary-child induction. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

def monicMultiply {m n : ℕ} (x : PolyPair m n) : Coeff (m+n) :=
  mulCLM (m+1) (n+1) (m+n) (monicPoly x.1) (monicPoly x.2)

lemma monicMultiply_eq_cut {m n : ℕ} (x : PolyPair m n) :
    monicMultiply x = cut (m+n) ((monicPoly x.1 : ℝ[X]) * (monicPoly x.2 : ℝ[X])) := rfl

theorem hasFDerivAt_monicMultiply {m n : ℕ} (x : PolyPair m n) :
    HasFDerivAt monicMultiply (monoSylv x) x := by
  let ins : PolyPair m n →L[ℝ] GlueInput m n :=
    (ContinuousLinearMap.id ℝ (PolyPair m n)).prod 0
  have h := ((hasFDerivAt_glue (ins x)).comp x ins.hasFDerivAt).fst
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  rfl

def monicMultiplyJacobian {m n : ℕ} (x : PolyPair m n) : ℝ :=
  (LinearMap.toMatrix (pairBasis m n) (degreeLT.basis ℝ (m+n))
    (fderiv ℝ monicMultiply x).toLinearMap).det

theorem monicMultiplyJacobian_eq {m n : ℕ} (x : PolyPair m n) :
    monicMultiplyJacobian x =
      Polynomial.resultant (monicPoly x.1) (monicPoly x.2) m n := by
  rw [monicMultiplyJacobian, (hasFDerivAt_monicMultiply x).fderiv]
  change (LinearMap.toMatrix (pairBasis m n) (degreeLT.basis ℝ (m+n))
    (sylvesterMap (monicPoly x.1) (monicPoly x.2)
      (bounded_natDegree _) (bounded_natDegree _))).det = _
  rw [pairBasis, Polynomial.toMatrix_sylvesterMap']
  rfl

theorem monicMultiply_reconstruct {m n : ℕ} (x : PolyPair m n) :
    (monicPoly (monicMultiply x) : ℝ[X]) =
      (monicPoly x.1 : ℝ[X]) * (monicPoly x.2 : ℝ[X]) := by
  rw [monicMultiply_eq_cut]
  apply monic_reconstruct
  · exact (monic_monicPoly x.1).mul (monic_monicPoly x.2)
  · rw [Polynomial.natDegree_mul (monic_monicPoly x.1).ne_zero (monic_monicPoly x.2).ne_zero,
      natDegree_monicPoly, natDegree_monicPoly]

end HydrologyTree
