import HydrologyTree.LeadingCoefficients
import HydrologyTree.BlockJacobian

/-! The monic-numerator scaling factor, including zero scale and degree zero. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scaleChart (x : ℝ × E) : ℝ × E := (x.1, x.1 • x.2)

def scaleChartDerivative (x : ℝ × E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    (x.1 • ContinuousLinearMap.snd ℝ ℝ E +
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight x.2)

/-- The actual derivative of multiplication of the lower coefficients by the scale. -/
theorem hasFDerivAt_scaleChart (x : ℝ × E) :
    HasFDerivAt scaleChart (scaleChartDerivative x) x := by
  exact (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.prodMk
    ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.smul
      (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)

lemma toMatrix_scaleChartDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (x : ℝ × E) :
    LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod b)
      ((Basis.singleton Unit ℝ).prod b) (scaleChartDerivative x).toLinearMap =
    Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) 0
      (Matrix.of fun i (_ : Unit) => b.repr x.2 i) (x.1 • (1 : Matrix ι ι ℝ)) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, scaleChartDerivative, Matrix.one_apply, Finsupp.single_apply, eq_comm]

/-- An all-dimensional, all-scale determinant identity, not a generic-rank statement. -/
theorem det_scaleChartDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (x : ℝ × E) :
    (LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod b)
      ((Basis.singleton Unit ℝ).prod b) (scaleChartDerivative x).toLinearMap).det =
      x.1 ^ Fintype.card ι := by
  rw [toMatrix_scaleChartDerivative, Matrix.det_fromBlocks_zero₁₂]
  simp [Matrix.det_smul]

end Generic

/-- Multiplication of an actual monic polynomial by its unrestricted scalar. -/
def scaleMonic {n : ℕ} (x : ℝ × Coeff n) : Coeff (n+1) := x.1 • monicPoly x.2

lemma scaleMonic_eq_comp {n : ℕ} :
    scaleMonic (n := n) = (leadingEquiv n) ∘ scaleChart := by
  funext x
  rw [scaleMonic, monicPoly_eq_leadingEquiv]
  symm
  simpa only [Function.comp_apply, scaleChart, Prod.smul_mk, smul_eq_mul, mul_one] using
    (leadingEquiv n).map_smul x.1 (1,x.2)

def scaleMonicDerivative {n : ℕ} (x : ℝ × Coeff n) :
    (ℝ × Coeff n) →L[ℝ] Coeff (n+1) :=
  (leadingEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scaleChartDerivative x)

theorem hasFDerivAt_scaleMonic {n : ℕ} (x : ℝ × Coeff n) :
    HasFDerivAt scaleMonic (scaleMonicDerivative x) x := by
  rw [scaleMonic_eq_comp]
  exact (leadingEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
    x (hasFDerivAt_scaleChart x)

lemma toMatrix_comp_equiv {E F G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (bE : Basis ι ℝ E) (bF : Basis κ ℝ F) (e : F ≃ₗ[ℝ] G) (L : E →ₗ[ℝ] F) :
    LinearMap.toMatrix bE (bF.map e) (e.toLinearMap.comp L) =
      LinearMap.toMatrix bE bF L := by
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.map_repr]

/-- The Jacobian in the manuscript's leading-first numerator coefficient order. -/
def monicScalingJacobian {n : ℕ} (x : ℝ × Coeff n) : ℝ :=
  (LinearMap.toMatrix ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ n))
    (leadingBasis n) (fderiv ℝ scaleMonic x).toLinearMap).det

/-- The exact factor c^n for a monic polynomial of degree n. -/
theorem monicScalingJacobian_eq {n : ℕ} (x : ℝ × Coeff n) :
    monicScalingJacobian x = x.1 ^ n := by
  rw [monicScalingJacobian, (hasFDerivAt_scaleMonic x).fderiv, leadingBasis]
  change (LinearMap.toMatrix _ _
    ((leadingEquiv n).toLinearMap.comp (scaleChartDerivative x).toLinearMap)).det = _
  rw [toMatrix_comp_equiv, det_scaleChartDerivative]
  simp

end HydrologyTree
