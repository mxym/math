import SchurCompletion.UnitaryHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Matrix.Order

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def orbitTensor (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (U : OneCopyUnitary D) : Matrix (Word D k) (Word D k) ℂ :=
  tensorMatrix ((U : Matrix (Fin D) (Fin D) ℂ) * X *
    (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) k

theorem continuous_orbitTensor (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Continuous (orbitTensor D k X) := by
  unfold orbitTensor tensorMatrix
  fun_prop

theorem integrable_orbitTensor (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Integrable (orbitTensor D k X) (unitaryHaar D) :=
  (continuous_orbitTensor D k X).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The literal matrix-valued Haar integral, with no ensemble or moment premise. -/
def haarOrbitAverage (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Word D k) (Word D k) ℂ :=
  ∫ U, orbitTensor D k X U ∂unitaryHaar D

def traceLeftLinear {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun Y := (A * Y).trace
  map_add' Y Z := by simp only [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Y := by simp only [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply,
    smul_eq_mul]

theorem haarOrbitAverage_traceLeft (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Word D k) (Word D k) ℂ) :
    (A * haarOrbitAverage D k X).trace =
      ∫ U, (A * orbitTensor D k X U).trace ∂unitaryHaar D :=
  ((traceLeftLinear A).toContinuousLinearMap.integral_comp_comm
    (integrable_orbitTensor D k X)).symm

theorem haarOrbitAverage_density (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) :
    (haarOrbitAverage D k X).PosSemidef ∧ (haarOrbitAverage D k X).trace = 1 := by
  have hOrbit (U : OneCopyUnitary D) :
      (orbitTensor D k X U).PosSemidef ∧ (orbitTensor D k X U).trace = 1 :=
    tensorMatrix_density _ (fixed_density_unitary_conjugate_density D X hX U) k
  constructor
  · exact (integral_nonneg (fun U => (hOrbit U).1.nonneg)).posSemidef
  · have h := haarOrbitAverage_traceLeft D k X 1
    simpa [Matrix.one_mul, (hOrbit _).2] using h

def leftMulLinear {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Y := A * Y
  map_add' Y Z := Matrix.mul_add _ _ _
  map_smul' c Y := Matrix.mul_smul _ _ _

theorem haarOrbitAverage_left_mul (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Word D k) (Word D k) ℂ) :
    A * haarOrbitAverage D k X =
      ∫ U, A * orbitTensor D k X U ∂unitaryHaar D :=
  ((leftMulLinear A).toContinuousLinearMap.integral_comp_comm
    (integrable_orbitTensor D k X)).symm

theorem haarOrbitAverage_common_support (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    rankBudgetProjector D k X.rank * haarOrbitAverage D k X = haarOrbitAverage D k X := by
  rw [haarOrbitAverage_left_mul]
  apply integral_congr_ae
  filter_upwards [] with U
  apply rankBudgetProjector_mul_tensorMatrix
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end
end ExtractionSchur
