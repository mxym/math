import SchurCompletion.HaarSupport

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def conjugateLinear {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Y := A * Y * Aᴴ
  map_add' Y Z := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Y := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem orbitTensor_mul (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (V U : OneCopyUnitary D) :
    orbitTensor D k X (V*U) = tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k *
      orbitTensor D k X U * (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ := by
  simp only [orbitTensor, Matrix.UnitaryGroup.mul_val, ← tensorMatrix_conjTranspose,
    ← tensorMatrix_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The actual Haar average commutes with the actual tensor-power unitary action. -/
theorem haarOrbitAverage_unitary_invariant (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (V : OneCopyUnitary D) :
    tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * haarOrbitAverage D k X *
      (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ = haarOrbitAverage D k X := by
  calc
    _ = ∫ U, tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * orbitTensor D k X U *
        (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ ∂unitaryHaar D :=
      ((conjugateLinear _).toContinuousLinearMap.integral_comp_comm
        (integrable_orbitTensor D k X)).symm
    _ = ∫ U, orbitTensor D k X (V*U) ∂unitaryHaar D := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact (orbitTensor_mul D k X V U).symm
    _ = _ := integral_mul_left_eq_self _ _

theorem haarOrbitAverage_commutes (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (V : OneCopyUnitary D) :
    tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * haarOrbitAverage D k X =
      haarOrbitAverage D k X * tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k := by
  have hV : (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ *
      tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k = 1 :=
    (tensorUnitary V k).prop.1
  have h := congrArg (fun Y => Y * tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)
    (haarOrbitAverage_unitary_invariant D k X V)
  simpa only [Matrix.mul_assoc, hV, Matrix.mul_one] using h

theorem haarOrbitAverage_orbit_pairing (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (U : OneCopyUnitary D) :
    (haarOrbitAverage D k X * orbitTensor D k X U).trace =
      (haarOrbitAverage D k X * tensorMatrix X k).trace := by
  have hU : (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ *
      tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k = 1 :=
    (tensorUnitary U k).prop.1
  simp only [orbitTensor, tensorMatrix_mul, tensorMatrix_conjTranspose]
  calc
    _ = ((haarOrbitAverage D k X * tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k) *
        tensorMatrix X k * (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k * haarOrbitAverage D k X) *
        tensorMatrix X k * (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ).trace := by
      rw [← haarOrbitAverage_commutes]
    _ = _ := by
      rw [Matrix.trace_mul_cycle]
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- A scalar, literal Haar integral for the average's second moment. This
does not assume a Schur block spectrum or a moment identity. -/
theorem haarOrbitAverage_trace_square (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    (haarOrbitAverage D k X * haarOrbitAverage D k X).trace =
      ∫ U : OneCopyUnitary D,
        (X * ((U : Matrix (Fin D) (Fin D) ℂ) * X *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace ^ k ∂unitaryHaar D := by
  calc
    _ = (haarOrbitAverage D k X * tensorMatrix X k).trace := by
      rw [haarOrbitAverage_traceLeft]
      simp only [haarOrbitAverage_orbit_pairing, integral_const, probReal_univ, one_smul]
    _ = (tensorMatrix X k * haarOrbitAverage D k X).trace := Matrix.trace_mul_comm _ _
    _ = ∫ U, (tensorMatrix X k * orbitTensor D k X U).trace ∂unitaryHaar D :=
      haarOrbitAverage_traceLeft D k X _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with U
      rw [orbitTensor, ← tensorMatrix_mul, actual_tensorMatrix_trace]

theorem haarOrbitAverage_rank_times_purity_ge_one (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    1 ≤ ((rankBudgetProjector D k X.rank).rank : ℝ) *
      (haarOrbitAverage D k X * haarOrbitAverage D k X).trace.re := by
  let P := rankBudgetProjector D k X.rank
  let Ω := haarOrbitAverage D k X
  have h := Extraction.hermitian_trace_pairing_sq_le P Ω
    (rankBudgetProjector_isHermitian D k X.rank) (haarOrbitAverage_density D k X hX).1.isHermitian
  have hP : P * P = P := rankBudgetProjector_idempotent D k X.rank
  have hPΩ : P * Ω = Ω := haarOrbitAverage_common_support D k X
  rw [hPΩ, (haarOrbitAverage_density D k X hX).2, Complex.one_re, one_pow,
    hP, hermitian_projection_trace_eq_rank P (rankBudgetProjector_isHermitian D k X.rank) hP] at h
  simpa only [Complex.natCast_re] using h

end
end ExtractionSchur
