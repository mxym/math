import RainsRealization.MeasurePrepare

open scoped BigOperators ComplexOrder Kronecker
open Matrix MinimaxProfile
namespace ExtractionRains
noncomputable section

@[simp] theorem bellProjector_trace (K : ℕ) [NeZero K] :
    (Extraction.bellProjector (d := Fin K)).trace = 1 :=
  (Extraction.bellProjector_density (d := Fin K)).2

/-- The normalized failure output, orthogonal to the maximally entangled target. -/
def failureState (K : ℕ) : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ :=
  (1 / ((K : ℝ)^2 - 1)) • (1 - Extraction.bellProjector)

/-- The actual Rains measure-and-prepare channel. -/
def channel {a b : ℕ} (K : ℕ) (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :=
  measurePrepare (Extraction.bellProjector (d := Fin K)) M +
    measurePrepare (failureState K) (1 - M)

theorem failureState_posSemidef (K : ℕ) (hK : 2 ≤ K) : (failureState K).PosSemidef := by
  letI : NeZero K := ⟨by omega⟩
  apply Extraction.one_sub_bellProjector_posSemidef.smul
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have : 0 < (K : ℝ)^2 - 1 := by nlinarith
  positivity

theorem failureState_trace (K : ℕ) (hK : 2 ≤ K) : (failureState K).trace = 1 := by
  letI : NeZero K := ⟨by omega⟩
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hn : (K : ℝ)^2 - 1 ≠ 0 := by nlinarith
  simp only [failureState, Matrix.trace_smul, Matrix.trace_sub, bellProjector_trace,
    Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Complex.real_smul, Nat.cast_mul]
  have hnc : ((K : ℂ)^2 - 1) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hnc]
  <;> ring

theorem channel_completelyPositive {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hM : Extraction.RainsEffect K M) :
    ExtractionCP.CompletelyPositive (channel K M) := by
  letI : NeZero K := ⟨by omega⟩
  exact completelyPositive_add
    (measurePrepare_completelyPositive _ _ (Extraction.bellProjector_density (d := Fin K)).1 hM.1)
    (measurePrepare_completelyPositive _ _ (failureState_posSemidef K hK) hM.2.1)

theorem channel_tracePreserving {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ExtractionCP.TracePreserving (channel K M) := by
  letI : NeZero K := ⟨by omega⟩
  intro X
  change ((measurePrepare Extraction.bellProjector M X) +
    measurePrepare (failureState K) (1-M) X).trace = X.trace
  rw [Matrix.trace_add, measurePrepare_trace, measurePrepare_trace,
    bellProjector_trace K, failureState_trace K hK]
  simp [Matrix.sub_mul, Matrix.trace_sub]

theorem bell_failureState_trace (K : ℕ) (hK : 2 ≤ K) :
    (Extraction.bellProjector * failureState K).trace = 0 := by
  letI : NeZero K := ⟨by omega⟩
  simp [failureState, Matrix.mul_smul, Matrix.mul_sub, Extraction.bellProjector_idempotent]

/-- Exact target overlap as a complex trace identity, on every complex matrix. -/
theorem channel_target_overlap {a b : ℕ} (K : ℕ) (hK : 2 ≤ K)
    (M X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (Extraction.bellProjector * channel K M X).trace = (M * X).trace := by
  letI : NeZero K := ⟨by omega⟩
  change (Extraction.bellProjector * ((M * X).trace • Extraction.bellProjector +
    ((1-M)*X).trace • failureState K)).trace = _
  simp [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Extraction.bellProjector_idempotent, bellProjector_trace K,
    bell_failureState_trace K hK]

end
end ExtractionRains
