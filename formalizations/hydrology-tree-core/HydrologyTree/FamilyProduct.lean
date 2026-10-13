import HydrologyTree.JacobianComposition

/-! Actual multiplication of arbitrarily many monic factors and its full
Fréchet Jacobian, with every degree and coefficient value allowed. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

@[reducible] def ProductInput : List ℕ → Type
  | [] => Coeff 0
  | m :: ms => Coeff m × ProductInput ms

instance productInputNormed : (ms : List ℕ) → NormedAddCommGroup (ProductInput ms)
  | [] => inferInstanceAs (NormedAddCommGroup (Coeff 0))
  | m :: ms => by
    letI := productInputNormed ms
    exact inferInstanceAs (NormedAddCommGroup (Coeff m × ProductInput ms))

instance productInputNormedSpace : (ms : List ℕ) → NormedSpace ℝ (ProductInput ms)
  | [] => inferInstanceAs (NormedSpace ℝ (Coeff 0))
  | m :: ms => by
    letI := productInputNormedSpace ms
    exact inferInstanceAs (NormedSpace ℝ (Coeff m × ProductInput ms))

def familyBasis : (ms : List ℕ) → Basis (Fin ms.sum) ℝ (ProductInput ms)
  | [] => degreeLT.basis ℝ 0
  | m :: ms => ((degreeLT.basis ℝ m).prod (familyBasis ms)).reindex finSumFinEquiv

/-- Low coefficients of the true product of all monic input polynomials. -/
def familyProduct : (ms : List ℕ) → ProductInput ms → Coeff ms.sum
  | [], _ => 0
  | m :: ms, x => monicMultiply (x.1, familyProduct ms x.2)

def familyProductDerivative : (ms : List ℕ) → (x : ProductInput ms) →
    ProductInput ms →L[ℝ] Coeff ms.sum
  | [], _ => 0
  | m :: ms, x =>
    (monoSylv (x.1, familyProduct ms x.2)).comp
      (keepLeft (E₀ := Coeff m) (familyProductDerivative ms x.2))

theorem hasFDerivAt_familyProduct (ms : List ℕ) (x : ProductInput ms) :
    HasFDerivAt (familyProduct ms) (familyProductDerivative ms x) x := by
  induction ms with
  | nil => exact hasFDerivAt_const (0 : Coeff 0) x
  | cons m ms ih =>
    have hfst := (ContinuousLinearMap.fst ℝ (Coeff m) (ProductInput ms)).hasFDerivAt (x := x)
    have hsnd := (ih x.2).comp x
      (ContinuousLinearMap.snd ℝ (Coeff m) (ProductInput ms)).hasFDerivAt
    exact (hasFDerivAt_monicMultiply (x.1,familyProduct ms x.2)).comp x (hfst.prodMk hsnd)

/-- All individual factors as actual polynomials, retaining possible repetitions. -/
def familyPolynomials : (ms : List ℕ) → ProductInput ms → List ℝ[X]
  | [], _ => []
  | _ :: ms, x => (monicPoly x.1 : ℝ[X]) :: familyPolynomials ms x.2

theorem familyProduct_reconstruct (ms : List ℕ) (x : ProductInput ms) :
    (monicPoly (familyProduct ms x) : ℝ[X]) = (familyPolynomials ms x).prod := by
  induction ms with
  | nil =>
    change (monicPoly (0 : Coeff 0) : ℝ[X]) = 1
    simp [coe_monicPoly]
  | cons m ms ih =>
    change (monicPoly (monicMultiply (x.1,familyProduct ms x.2)) : ℝ[X]) = _
    rw [monicMultiply_reconstruct, ih]
    rfl

/-- Resultant product in recursive factor-versus-remaining-product form. -/
def familyResultant : (ms : List ℕ) → ProductInput ms → ℝ
  | [], _ => 1
  | m :: ms, x =>
    Polynomial.resultant (monicPoly x.1) (monicPoly (familyProduct ms x.2)) m ms.sum *
      familyResultant ms x.2

lemma det_monoSylv {m n : ℕ} (x : PolyPair m n) :
    (LinearMap.toMatrix (pairBasis m n) (degreeLT.basis ℝ (m+n))
      (monoSylv x).toLinearMap).det =
        Polynomial.resultant (monicPoly x.1) (monicPoly x.2) m n := by
  simpa only [monicMultiplyJacobian, (hasFDerivAt_monicMultiply x).fderiv] using
    monicMultiplyJacobian_eq x

theorem det_familyProductDerivative (ms : List ℕ) (x : ProductInput ms) :
    (LinearMap.toMatrix (familyBasis ms) (degreeLT.basis ℝ ms.sum)
      (familyProductDerivative ms x).toLinearMap).det = familyResultant ms x := by
  induction ms with
  | nil =>
    change (LinearMap.toMatrix (degreeLT.basis ℝ 0) (degreeLT.basis ℝ 0)
      (0 : Coeff 0 →ₗ[ℝ] Coeff 0)).det = 1
    simp
  | cons m ms ih =>
    change (LinearMap.toMatrix (((degreeLT.basis ℝ m).prod (familyBasis ms)).reindex finSumFinEquiv)
      (degreeLT.basis ℝ (m+ms.sum))
      ((monoSylv (x.1,familyProduct ms x.2)).toLinearMap.comp
        (keepLeft (E₀ := Coeff m) (familyProductDerivative ms x.2)).toLinearMap)).det =
      _ * familyResultant ms x.2
    rw [LinearMap.toMatrix_comp
      (((degreeLT.basis ℝ m).prod (familyBasis ms)).reindex finSumFinEquiv) (pairBasis m ms.sum)
      (degreeLT.basis ℝ (m+ms.sum)), Matrix.det_mul, det_monoSylv]
    congr 1
    rw [pairBasis, det_both_reindex, det_keepLeft, ih]

/-- The determinant is taken from fderiv of the actual coefficient map. -/
def familyProductJacobian (ms : List ℕ) (x : ProductInput ms) : ℝ :=
  (LinearMap.toMatrix (familyBasis ms) (degreeLT.basis ℝ ms.sum)
    (fderiv ℝ (familyProduct ms) x).toLinearMap).det

theorem familyProductJacobian_eq (ms : List ℕ) (x : ProductInput ms) :
    familyProductJacobian ms x = familyResultant ms x := by
  rw [familyProductJacobian, (hasFDerivAt_familyProduct ms x).fderiv,
    det_familyProductDerivative]

end HydrologyTree
