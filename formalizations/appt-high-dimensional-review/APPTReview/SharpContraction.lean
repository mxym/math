import APPTReview.ProjectionState
import APPT.Quantum.Permutation

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a : Type*} [Fintype a] [DecidableEq a]

def exchangeOperator : Matrix (a × a) (a × a) ℂ :=
  APPT.Quantum.permMatrix (Equiv.prodComm a a)

theorem exchangeOperator_hermitian : (exchangeOperator (a:=a)).IsHermitian := by
  unfold exchangeOperator Matrix.IsHermitian
  rw [APPT.Quantum.permMatrix_conjTranspose]
  rfl

theorem exchangeOperator_sq : exchangeOperator (a:=a)*exchangeOperator=1 := by
  have hh := APPT.Quantum.permMatrix_mul_conjTranspose (Equiv.prodComm a a)
  change exchangeOperator * exchangeOperatorᴴ = 1 at hh
  rwa [exchangeOperator_hermitian.eq] at hh

noncomputable def antisymmetricProjection : Matrix (a × a) (a × a) ℂ :=
  (1/2 : ℝ) • (1-exchangeOperator)

theorem antisymmetricProjection_hermitian : (antisymmetricProjection (a:=a)).IsHermitian := by
  exact (Matrix.isHermitian_one.sub exchangeOperator_hermitian).smul (show IsSelfAdjoint (1/2 : ℝ) by rfl)

theorem antisymmetricProjection_sq : antisymmetricProjection (a:=a)*antisymmetricProjection=antisymmetricProjection := by
  unfold antisymmetricProjection
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_one, exchangeOperator_sq]
  module

def diagonalVector (p : a × a) : ℂ := if p.1=p.2 then 1 else 0

theorem transpose_exchange : APPT.Quantum.partialTranspose (exchangeOperator (a:=a)) =
    Matrix.vecMulVec diagonalVector (star diagonalVector) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hi : i=x <;> by_cases hj : j=y <;>
    simp_all [APPT.Quantum.partialTranspose, exchangeOperator, APPT.Quantum.permMatrix,
      Matrix.vecMulVec, diagonalVector, ite_and, eq_comm]

/-- Exact physical test on the antisymmetric projection, without normalization. -/
theorem antisymmetric_quadratic (c : ℝ) :
    star (diagonalVector (a:=a)) ⬝ᵥ
      (APPT.Quantum.partialTranspose (c • (1 : Matrix (a × a) (a × a) ℂ)+
        (2 : ℝ) • antisymmetricProjection) *ᵥ diagonalVector) =
      ((Fintype.card a : ℂ)*((c : ℂ)+1-(Fintype.card a : ℂ))) := by
  have he : c • (1 : Matrix (a × a) (a × a) ℂ)+(2 : ℝ) • antisymmetricProjection =
      (c+1) • (1 : Matrix (a × a) (a × a) ℂ)-exchangeOperator := by
    unfold antisymmetricProjection
    module
  rw [he, APPT.Quantum.partialTranspose_sub, APPT.Quantum.partialTranspose_smul,
    APPT.Quantum.partialTranspose_one, transpose_exchange]
  simp [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec, diagonalVector, Fintype.sum_prod_type, Complex.real_smul,
    mul_ite, ite_mul, Finset.sum_sub_distrib]
  <;> push_cast <;> ring

/-- The dimension constant cannot be decreased, even for a genuine projection. -/
theorem antisymmetric_not_ppt {c : ℝ} (ha : 0<Fintype.card a)
    (hc : c<(Fintype.card a : ℝ)-1) :
    ¬ (APPT.Quantum.partialTranspose
      (c • (1 : Matrix (a × a) (a × a) ℂ)+(2 : ℝ) • antisymmetricProjection)).PosSemidef := by
  intro hp
  have hh := hp.dotProduct_mulVec_nonneg diagonalVector
  rw [antisymmetric_quadratic] at hh
  have hr : (0 : ℝ) ≤ (Fintype.card a : ℝ)*(c+1-Fintype.card a) := by
    exact_mod_cast hh
  have hpos : (0 : ℝ)<Fintype.card a := by exact_mod_cast ha
  have hneg : (Fintype.card a : ℝ)*(c+1-Fintype.card a)<0 :=
    mul_neg_of_pos_of_neg hpos (by linarith)
  linarith

theorem antisymmetricProjection_trace : (antisymmetricProjection (a:=a)).trace =
    (((Fintype.card a : ℂ)^2-Fintype.card a)/2) := by
  have hf : (exchangeOperator (a:=a)).trace = (Fintype.card a : ℂ) := by
    change (∑ p : a × a, if (Equiv.prodComm a a) p = p then (1 : ℂ) else 0) = _
    rw [Fintype.sum_prod_type]
    simp [eq_comm]
  simp [antisymmetricProjection, Matrix.trace_smul, Matrix.trace_sub, hf,
    Matrix.trace_one, Complex.real_smul]
  ring

/-- Actual positive density used to reject an incorrect dimension-three extension. -/
noncomputable def wrongDimensionState : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (1/22 : ℝ) • (1+antisymmetricProjection)

theorem wrongDimensionState_density : APPT.Quantum.IsDensity wrongDimensionState := by
  constructor
  · exact (Matrix.PosSemidef.one.add
      (hermitian_idempotent_posSemidef _ antisymmetricProjection_hermitian
        antisymmetricProjection_sq)).smul (by norm_num : (0 : ℝ)≤1/22)
  · norm_num [wrongDimensionState, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_one, antisymmetricProjection_trace, Complex.real_smul]

theorem wrongDimensionState_not_appt : ¬ APPT.Quantum.AbsolutelyPPT wrongDimensionState := by
  intro h
  have hp : (APPT.Quantum.partialTranspose wrongDimensionState).PosSemidef := by
    simpa using h (1 : Matrix.unitaryGroup (Fin 4 × Fin 4) ℂ)
  have he : (44 : ℝ) • wrongDimensionState =
      (2 : ℝ) • (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)+
        (2 : ℝ) • antisymmetricProjection := by
    unfold wrongDimensionState
    module
  have hs := hp.smul (by norm_num : (0 : ℝ)≤44)
  rw [← APPT.Quantum.partialTranspose_smul, he] at hs
  exact antisymmetric_not_ppt (by norm_num) (by norm_num : (2 : ℝ)<(Fintype.card (Fin 4) : ℝ)-1) hs

end APPTReview
