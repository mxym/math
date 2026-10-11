import HydrologyTree.Scaling
import HydrologyTree.Triangular

/-! The actual coefficient transformation P=(X+d)F-N at a rooted compartment. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rootChart (C : E →L[ℝ] ℝ) (D : E →L[ℝ] E) (x : E × (ℝ × E)) : E × (ℝ × E) :=
  (x.1, (x.2.1 + C x.1, D x.1 + x.2.1 • x.1 - x.2.2))

def rootFiber (f : E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    ((ContinuousLinearMap.fst ℝ ℝ E).smulRight f - ContinuousLinearMap.snd ℝ ℝ E)

@[simp] lemma rootFiber_apply (f : E) (h : ℝ × E) :
    rootFiber f h = (h.1, h.1 • f - h.2) := rfl

def rootChartDerivative (C : E →L[ℝ] ℝ) (D : E →L[ℝ] E) (x : E × (ℝ × E)) :
    (E × (ℝ × E)) →L[ℝ] (E × (ℝ × E)) :=
  lowerBlock (ContinuousLinearMap.id ℝ E)
    (C.prod (D + x.2.1 • ContinuousLinearMap.id ℝ E)) (rootFiber x.1)

/-- This is the Frechet derivative of the actual root coefficient operation. -/
theorem hasFDerivAt_rootChart (C : E →L[ℝ] ℝ) (D : E →L[ℝ] E) (x : E × (ℝ × E)) :
    HasFDerivAt (rootChart C D) (rootChartDerivative C D x) x := by
  let F : (E × (ℝ × E)) →L[ℝ] E := ContinuousLinearMap.fst ℝ E (ℝ × E)
  let B : (E × (ℝ × E)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ E (ℝ × E))
  let N : (E × (ℝ × E)) →L[ℝ] E :=
    (ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ E (ℝ × E))
  have hb := B.hasFDerivAt.add (C.hasFDerivAt.comp x F.hasFDerivAt)
  have hn := ((D.hasFDerivAt.comp x F.hasFDerivAt).add
    (B.hasFDerivAt.smul F.hasFDerivAt)).sub N.hasFDerivAt
  apply (F.hasFDerivAt.prodMk (hb.prodMk hn)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change h.2.1 + C h.1 = C h.1 + h.2.1
      abel
    · change D h.1 + (x.2.1 • h.1 + h.2.1 • x.1) - h.2.2 =
        (D h.1 + x.2.1 • h.1) + (h.2.1 • x.1 - h.2.2)
      abel

lemma toMatrix_rootFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (f : E) :
    LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod b)
      ((Basis.singleton Unit ℝ).prod b) (rootFiber f).toLinearMap =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) 0
        (Matrix.of fun i (_ : Unit) => b.repr f i) (-1 : Matrix ι ι ℝ) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, rootFiber, Matrix.one_apply, Matrix.of_apply, Finsupp.single_apply, eq_comm]

theorem det_rootFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (f : E) :
    (LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod b)
      ((Basis.singleton Unit ℝ).prod b) (rootFiber f).toLinearMap).det =
      (-1 : ℝ) ^ Fintype.card ι := by
  rw [toMatrix_rootFiber, Matrix.det_fromBlocks_zero₁₂]
  simp [Matrix.det_neg]

/-- The root operation is a polynomial coordinate change with determinant ±1
at every coefficient vector, not just away from a discriminant or zero rates. -/
theorem det_rootChartDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (C : E →L[ℝ] ℝ) (D : E →L[ℝ] E) (x : E × (ℝ × E)) :
    (LinearMap.toMatrix (b.prod ((Basis.singleton Unit ℝ).prod b))
      (b.prod ((Basis.singleton Unit ℝ).prod b))
      (rootChartDerivative C D x).toLinearMap).det = (-1 : ℝ) ^ Fintype.card ι := by
  rw [rootChartDerivative, det_lowerBlock, det_rootFiber]
  simp

end Generic

/-- Coefficient crossing the truncation boundary when a polynomial is multiplied by X. -/
def shiftTop (n : ℕ) : Coeff n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((Polynomial.lcoeff ℝ n).comp (LinearMap.mulLeft ℝ (X : ℝ[X]))).comp (degreeLT ℝ n).subtype)

/-- Lower coefficients of the actual polynomial X*f. -/
def shiftLow (n : ℕ) : Coeff n →L[ℝ] Coeff n :=
  LinearMap.toContinuousLinearMap
    (((cut n).comp (LinearMap.mulLeft ℝ (X : ℝ[X]))).comp (degreeLT ℝ n).subtype)

/-- Physical Schur-complement root polynomial, before any response cancellation. -/
def rootPolynomial {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) : ℝ[X] :=
  (X + C x.2.1) * (monicPoly x.1 : ℝ[X]) - (x.2.2 : ℝ[X])

lemma rootPolynomial_cut {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    cut n (rootPolynomial x) = shiftLow n x.1 + x.2.1 • x.1 - x.2.2 := by
  simp only [rootPolynomial, coe_monicPoly, add_mul, mul_add, map_sub, map_add]
  rw [show (X : ℝ[X]) * X^n = X^(n+1) by rw [pow_succ'],
    cut_X_pow_of_le n (n+1) (by omega)]
  rw [← smul_eq_C_mul, map_smul, cut_X_pow_of_le n n le_rfl, smul_zero]
  rw [← smul_eq_C_mul, map_smul, cut_coe, cut_coe]
  change 0 + 0 + (shiftLow n x.1 + x.2.1 • x.1) - x.2.2 = _
  abel

lemma rootPolynomial_coeff_next {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    (rootPolynomial x).coeff n = x.2.1 + shiftTop n x.1 := by
  simp only [rootPolynomial, coe_monicPoly, add_mul, mul_add,
    Polynomial.coeff_sub, Polynomial.coeff_add]
  rw [show (X : ℝ[X]) * X^n = X^(n+1) by rw [pow_succ']]
  simp only [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
    coeff_eq_zero_of_bound x.1 le_rfl, coeff_eq_zero_of_bound x.2.2 le_rfl,
    if_pos rfl, if_neg (show n ≠ n+1 from by omega), mul_one, mul_zero,
    sub_zero, add_zero, zero_add]
  simp only [ite_true, mul_one]
  rfl

/-- The actual (unreduced) root polynomial coefficient chart. -/
def rootCoefficientMap {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    Coeff n × (ℝ × Coeff n) :=
  (x.1, ((rootPolynomial x).coeff n, cut n (rootPolynomial x)))

lemma rootCoefficientMap_eq {n : ℕ} :
    rootCoefficientMap (n := n) = rootChart (shiftTop n) (shiftLow n) := by
  funext x
  simp [rootCoefficientMap, rootChart, rootPolynomial_cut, rootPolynomial_coeff_next]

theorem hasFDerivAt_rootCoefficientMap {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    HasFDerivAt rootCoefficientMap (rootChartDerivative (shiftTop n) (shiftLow n) x) x := by
  rw [rootCoefficientMap_eq]
  exact hasFDerivAt_rootChart _ _ _

def rootCoefficientJacobian {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) : ℝ :=
  (LinearMap.toMatrix
    ((degreeLT.basis ℝ n).prod ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ n)))
    ((degreeLT.basis ℝ n).prod ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ n)))
    (fderiv ℝ rootCoefficientMap x).toLinearMap).det

/-- The true polynomial coefficient-map derivative has determinant (-1)^n,
without assuming invertibility, positivity, or absence of common roots. -/
theorem rootCoefficientJacobian_eq {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    rootCoefficientJacobian x = (-1 : ℝ)^n := by
  rw [rootCoefficientJacobian, (hasFDerivAt_rootCoefficientMap x).fderiv,
    det_rootChartDerivative]
  simp

lemma degree_rootProduct {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    ((X + C x.2.1) * (monicPoly x.1 : ℝ[X])).degree = ((n+1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_mul, Polynomial.degree_X_add_C,
    Polynomial.degree_eq_natDegree (monic_monicPoly x.1).ne_zero,
    natDegree_monicPoly]
  simp [Nat.cast_add, add_comm]

lemma rootNumerator_degree_lt {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    (x.2.2 : ℝ[X]).degree < ((X + C x.2.1) * (monicPoly x.1 : ℝ[X])).degree := by
  rw [degree_rootProduct]
  exact (Polynomial.mem_degreeLT.mp x.2.2.property).trans_le (by exact_mod_cast Nat.le_succ n)

/-- The root update never drops degree, including zero edge rates. -/
theorem rootPolynomial_monic {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    (rootPolynomial x).Monic := by
  exact ((Polynomial.monic_X_add_C x.2.1).mul (monic_monicPoly x.1)).sub_of_left
    (rootNumerator_degree_lt x)

theorem rootPolynomial_natDegree {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    (rootPolynomial x).natDegree = n+1 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [rootPolynomial, Polynomial.degree_sub_eq_left_of_degree_lt (rootNumerator_degree_lt x),
    degree_rootProduct]

/-- The checked coefficient map determines the entire actual root polynomial. -/
theorem rootPolynomial_reconstruct {n : ℕ} (x : Coeff n × (ℝ × Coeff n)) :
    (monicPoly (cut (n+1) (rootPolynomial x)) : ℝ[X]) = rootPolynomial x :=
  monic_reconstruct _ (rootPolynomial_monic x) (rootPolynomial_natDegree x)

end HydrologyTree
