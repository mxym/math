import RainsRealization.Channel

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace ExtractionRains
noncomputable section

@[simp] theorem partialTranspose_complex_smul {a b : Type} (z : ℂ)
    (X : Matrix (a × b) (a × b) ℂ) :
    APPT.Quantum.partialTranspose (z • X) = z • APPT.Quantum.partialTranspose X := rfl

def plusProjection (K : ℕ) : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ :=
  (1 / 2 : ℝ) • (1 + Extraction.swapMatrix)

def minusProjection (K : ℕ) : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ :=
  (1 / 2 : ℝ) • (1 - Extraction.swapMatrix)

def plusEffect {a b : ℕ} (K : ℕ) (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  (1 / ((K : ℝ) + 1)) • ((1 / (K : ℝ)) • 1 + APPT.Quantum.partialTranspose M)

def minusEffect {a b : ℕ} (K : ℕ) (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  (1 / ((K : ℝ) - 1)) • ((1 / (K : ℝ)) • 1 - APPT.Quantum.partialTranspose M)

theorem plusProjection_posSemidef (K : ℕ) : (plusProjection K).PosSemidef :=
  Extraction.one_add_swapMatrix_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1/2)

theorem minusProjection_posSemidef (K : ℕ) : (minusProjection K).PosSemidef :=
  Extraction.one_sub_swapMatrix_posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1/2)

theorem plusEffect_posSemidef {a b : ℕ} (K : ℕ)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M) :
    (plusEffect K M).PosSemidef := by
  exact hM.2.2.1.smul (by positivity : (0 : ℝ) ≤ 1 / ((K : ℝ) + 1))

theorem minusEffect_posSemidef {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M) :
    (minusEffect K M).PosSemidef := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  exact hM.2.2.2.smul (one_div_nonneg.mpr (by linarith))

theorem pt_channel_formula {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ExtractionCP.ptConjugate (channel K M) X =
      (APPT.Quantum.partialTranspose M * X).trace •
        ((1 / (K : ℝ)) • Extraction.swapMatrix (d := Fin K)) +
      (X.trace - (APPT.Quantum.partialTranspose M * X).trace) •
        ((1 / ((K : ℝ)^2 - 1)) • (1 - (1 / (K : ℝ)) • Extraction.swapMatrix)) := by
  letI : NeZero K := ⟨by omega⟩
  change APPT.Quantum.partialTranspose
    ((M * APPT.Quantum.partialTranspose X).trace • Extraction.bellProjector +
      ((1-M) * APPT.Quantum.partialTranspose X).trace • failureState K) = _
  rw [APPT.Quantum.partialTranspose_add, partialTranspose_complex_smul,
    partialTranspose_complex_smul]
  simp only [failureState, APPT.Quantum.partialTranspose_smul,
    APPT.Quantum.partialTranspose_sub, APPT.Quantum.partialTranspose_one,
    Extraction.partialTranspose_bellProjector, Fintype.card_fin,
    Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    APPT.Quantum.partialTranspose_trace, Extraction.trace_partialTranspose_pairing]

/-- Exact positive measure-and-prepare decomposition of the transpose conjugate.
The Rains intervals supply the two positive input effects. -/
theorem pt_channel_decomposition {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ExtractionCP.ptConjugate (channel K M) =
      measurePrepare (plusProjection K) (plusEffect K M) +
      measurePrepare (minusProjection K) (minusEffect K M) := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hz : (K : ℂ) ≠ 0 := by exact_mod_cast (show (K : ℝ) ≠ 0 by linarith)
  have hp : (K : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (K : ℝ) + 1 ≠ 0 by linarith)
  have hm : (K : ℂ) - 1 ≠ 0 := by exact_mod_cast (show (K : ℝ) - 1 ≠ 0 by linarith)
  have hn : (K : ℂ)^2 - 1 ≠ 0 := by exact_mod_cast (show (K : ℝ)^2 - 1 ≠ 0 by nlinarith)
  ext X p q
  rw [pt_channel_formula K hK]
  simp only [LinearMap.add_apply, measurePrepare_apply, plusProjection, minusProjection,
    plusEffect, minusEffect, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp [hz,hp,hm,hn]
  <;> ring

theorem channel_pt_completelyPositive {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M) :
    ExtractionCP.CompletelyPositive (ExtractionCP.ptConjugate (channel K M)) := by
  rw [pt_channel_decomposition K hK]
  exact completelyPositive_add
    (measurePrepare_completelyPositive _ _ (plusProjection_posSemidef K)
      (plusEffect_posSemidef K M hM))
    (measurePrepare_completelyPositive _ _ (minusProjection_posSemidef K)
      (minusEffect_posSemidef K hK M hM))

end
end ExtractionRains
