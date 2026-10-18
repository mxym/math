import OperationalCompletion.OptimalFidelity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import APPTReview.StateTopology

open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator
open Matrix MinimaxProfile MeasureTheory
namespace OperationalCompletion
noncomputable section

variable {a b K : ℕ}

def protocolFidelityLinear (V : KrausPPTProtocol a b K) :
    Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ →ₗ[ℝ] ℝ where
  toFun := V.fidelity
  map_add' X Y := by
    simp [KrausPPTProtocol.fidelity,overlap,Extraction.krausApply,
      Matrix.mul_add,Matrix.add_mul,Finset.sum_add_distrib]
  map_smul' c X := by
    exact overlap_real_smul V.A V.U X c

def matrixTraceLinear {ι : Type*} [Fintype ι] : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun := Matrix.trace
  map_add' X Y := Matrix.trace_add X Y
  map_smul' c X := Matrix.trace_smul c X

/-- An actual probability barycenter, with no finite-support assumption. -/
def probabilityAverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) := ∫ ω,X ω ∂μ

/-- Density matrices are uniformly bounded; measurable probability ensembles
therefore need no separately supplied integrability certificate. -/
theorem density_ensemble_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hXm : AEStronglyMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ,APPT.Quantum.IsDensity (X ω)) : Integrable X μ := by
  obtain ⟨B,hB⟩ := (APPTReview.isCompact_density (a:=Fin a) (b:=Fin b)).isBounded.exists_norm_le
  exact Integrable.of_bound hXm B (hX.mono fun _ h => hB _ h)

theorem probabilityAverage_density {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hXi : Integrable X μ)
    (hX : ∀ᵐ ω ∂μ,APPT.Quantum.IsDensity (X ω)) :
    APPT.Quantum.IsDensity (probabilityAverage μ X) := by
  constructor
  · have hconv : Convex ℝ {A : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ | A.PosSemidef} := by
      intro A hA B hB c d hc hd _
      exact (hA.smul hc).add (hB.smul hd)
    exact hconv.integral_mem Matrix.posSemidef_is_closed (hX.mono fun _ h => h.1) hXi
  · change (∫ ω,X ω ∂μ).trace=1
    calc
      _ = ∫ ω,(X ω).trace ∂μ := by
        simpa [matrixTraceLinear] using
          (matrixTraceLinear.toContinuousLinearMap.integral_comp_comm hXi).symm
      _ = 1 := by
        rw [integral_congr_ae (hX.mono fun _ h => h.2)]
        simp

theorem fidelity_probabilityAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : KrausPPTProtocol a b K)
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hXi : Integrable X μ) :
    V.fidelity (probabilityAverage μ X)=∫ ω,V.fidelity (X ω) ∂μ :=
  ((protocolFidelityLinear V).toContinuousLinearMap.integral_comp_comm hXi).symm

/-- A uniform physical guarantee is no larger than its genuine probability
ensemble average. The parameter space and distribution are arbitrary. -/
theorem guarantee_le_probabilityAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : KrausPPTProtocol a b K)
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hXi : Integrable X μ)
    (c : ℝ) (hc : ∀ᵐ ω ∂μ,c≤V.fidelity (X ω)) :
    c≤V.fidelity (probabilityAverage μ X) := by
  rw [fidelity_probabilityAverage μ V X hXi]
  have hi := (protocolFidelityLinear V).toContinuousLinearMap.integrable_comp hXi
  change Integrable (fun ω => V.fidelity (X ω)) μ at hi
  have hh : (∫ _ : Ω,c ∂μ)≤∫ ω,V.fidelity (X ω) ∂μ :=
    integral_mono_ae (integrable_const c) hi hc
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- The actual density-matrix Rains/purity envelope for any integrable
probability ensemble, uniformly over the preprocessing unitary and channel. -/
theorem physical_probability_ensemble_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hK : 0<K)
    (V : KrausPPTProtocol a b K)
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hXi : Integrable X μ)
    (hX : ∀ᵐ ω ∂μ,APPT.Quantum.IsDensity (X ω))
    (c : ℝ) (hc : ∀ᵐ ω ∂μ,c≤V.fidelity (X ω)) :
    c≤min 1 (min ((a:ℝ)/K)
      (Real.sqrt (((probabilityAverage μ X)*(probabilityAverage μ X)).trace.re *
        ((a*b:ℝ)/(K:ℝ)^2)))) := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  apply (guarantee_le_probabilityAverage μ V X hXi c hc).trans
  have hb := ExtractionLocalCap.kraus_target_overlap_full_envelope V.A V.complete V.ptPositive
    (probabilityAverage μ X) (probabilityAverage_density μ X hXi hX) V.U
  simpa only [KrausPPTProtocol.fidelity,overlap,Fintype.card_fin] using hb

theorem measurable_physical_ensemble_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hK : 0<K)
    (V : KrausPPTProtocol a b K)
    (X : Ω → Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hXm : AEStronglyMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ,APPT.Quantum.IsDensity (X ω))
    (c : ℝ) (hc : ∀ᵐ ω ∂μ,c≤V.fidelity (X ω)) :
    c≤min 1 (min ((a:ℝ)/K)
      (Real.sqrt (((probabilityAverage μ X)*(probabilityAverage μ X)).trace.re *
        ((a*b:ℝ)/(K:ℝ)^2)))) :=
  physical_probability_ensemble_bound μ hK V X (density_ensemble_integrable μ X hXm hX) hX c hc

end
end OperationalCompletion
