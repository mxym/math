import HydrologyTree.CatenaryJacobian

/-! Transport to the usual ascending coefficient and physical-array bases.
The conversion factor is explicit, nonzero and depends only on the number of
compartments, never on the rates. No change of the physical coefficient map. -/
open Module Matrix Polynomial
noncomputable section
namespace HydrologyTree

abbrev CatenaryArrayIndex (n : ℕ) := Fin (n+1) ⊕ Fin n

def catenaryArrayInputBasis (n : ℕ) : Basis (CatenaryArrayIndex n) ℝ (TreeRates n) :=
  (Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n))

def catenaryArrayOutputBasis (n : ℕ) : Basis (CatenaryArrayIndex n) ℝ (PathCoefficients n) :=
  (degreeLT.basis ℝ (n+1)).prod (degreeLT.basis ℝ n)

/-- Usual physical rate arrays and ascending non-leading P/F coefficients. -/
def catenaryCanonicalJacobian (n : ℕ) (x : TreeRates n) : ℝ :=
  (LinearMap.toMatrix (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
    (fderiv ℝ (pathCoefficientMap n) x).toLinearMap).det

/-- Explicit linear coefficient permutation, independent of all rate parameters. -/
def catenaryCoordinateReturn (n : ℕ) : PathCoefficients n ≃ₗ[ℝ] TreeRates n :=
  (pathCoefficientEquiv n).trans (pathRateEquiv n)

def catenaryCoordinateDet (n : ℕ) : ℝ :=
  (LinearMap.toMatrix (catenaryArrayOutputBasis n) (catenaryArrayInputBasis n)
    (catenaryCoordinateReturn n).toLinearMap).det

lemma catenaryCoordinateDet_ne_zero (n : ℕ) : catenaryCoordinateDet n ≠ 0 := by
  let e := catenaryCoordinateReturn n
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hm := congrArg
    (LinearMap.toMatrix (catenaryArrayInputBasis n) (catenaryArrayInputBasis n)) he
  rw [LinearMap.toMatrix_comp (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
    (catenaryArrayInputBasis n), LinearMap.toMatrix_id] at hm
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  change catenaryCoordinateDet n * _ = 1 at hd
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

lemma array_normalized_jacobian (n : ℕ) (x : TreeRates n) :
    endJacobian (fun y => catenaryCoordinateReturn n (pathCoefficientMap n y)) x =
      catenaryCoordinateDet n * catenaryCanonicalJacobian n x := by
  have h := (catenaryCoordinateReturn n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    (differentiable_pathCoefficientMap n x).hasFDerivAt
  have hd : fderiv ℝ (fun y => catenaryCoordinateReturn n (pathCoefficientMap n y)) x =
      (catenaryCoordinateReturn n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (pathCoefficientMap n) x) := h.fderiv
  rw [endJacobian, hd, ← LinearMap.det_toMatrix (catenaryArrayInputBasis n)]
  change (LinearMap.toMatrix _ _ ((catenaryCoordinateReturn n).toLinearMap.comp
    (fderiv ℝ (pathCoefficientMap n) x).toLinearMap)).det = _
  rw [LinearMap.toMatrix_comp (catenaryArrayInputBasis n) (catenaryArrayOutputBasis n)
    (catenaryArrayInputBasis n), Matrix.det_mul]
  rfl

lemma catenaryCanonicalJacobian_transport (n : ℕ) (x : TreeRates n) :
    catenaryCoordinateDet n * catenaryCanonicalJacobian n x =
      pathOrientation n * pathRateMonomial n x := by
  have h := endJacobian_conjugate (pathRateEquiv n).toContinuousLinearEquiv
    (normalizedPhysicalPath n) x
    (differentiable_normalizedPhysicalPath n ((pathRateEquiv n).symm x))
  have he : (fun y => (pathRateEquiv n) (normalizedPhysicalPath n ((pathRateEquiv n).symm y))) =
      (fun y => catenaryCoordinateReturn n (pathCoefficientMap n y)) := by
    funext y
    simp [normalizedPhysicalPath, catenaryCoordinateReturn]
  change endJacobian (fun y => (pathRateEquiv n) (normalizedPhysicalPath n ((pathRateEquiv n).symm y))) x = _ at h
  rw [he, array_normalized_jacobian, normalizedPhysicalPath_jacobian,
    pathWeight_eq_rate_monomial] at h
  have hh : (pathRateEquiv n) ((pathRateEquiv n).toContinuousLinearEquiv.symm x) = x :=
    (pathRateEquiv n).apply_symm_apply x
  rwa [hh] at h

/-- A fixed explicit nonzero constant for the chosen ascending coordinate order. -/
def catenaryCanonicalFactor (n : ℕ) : ℝ := pathOrientation n / catenaryCoordinateDet n

lemma catenaryCanonicalFactor_ne_zero (n : ℕ) : catenaryCanonicalFactor n ≠ 0 :=
  div_ne_zero (pathOrientation_ne_zero n) (catenaryCoordinateDet_ne_zero n)

/-- In standard ascending coefficient and physical-array coordinates, the exact
Jacobian has precisely the conjectured monomial, with an explicit nonzero
size-dependent constant. There are no additional parameter-dependent factors. -/
theorem catenaryCanonicalJacobian_eq (n : ℕ) (x : TreeRates n) :
    catenaryCanonicalJacobian n x = catenaryCanonicalFactor n *
      ∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1) := by
  have h := catenaryCanonicalJacobian_transport n x
  have he : catenaryCanonicalJacobian n x =
      (pathOrientation n * pathRateMonomial n x) / catenaryCoordinateDet n := by
    apply (eq_div_iff (catenaryCoordinateDet_ne_zero n)).mpr
    simpa only [mul_comm] using h
  rw [he, catenaryCanonicalFactor, pathRateMonomial]
  ring

/-- Exact standard-coordinate singular locus, including the zero-rate boundary. -/
theorem catenaryCanonicalJacobian_zero_iff (n : ℕ) (x : TreeRates n) :
    catenaryCanonicalJacobian n x = 0 ↔
      (∃ i : Fin n, x.1 i.succ = 0) ∨
      (∃ i : Fin n, i.val+1 < n ∧ x.2 i = 0) := by
  rw [catenaryCanonicalJacobian_eq, mul_eq_zero]
  simp only [catenaryCanonicalFactor_ne_zero, false_or]
  exact pathRateMonomial_zero_iff n x

end HydrologyTree
