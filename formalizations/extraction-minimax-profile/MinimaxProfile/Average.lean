import LocalCap.ActualCap
import SpectralProtocol.ProductPPT
import MinimaxProfile.Profile

open scoped BigOperators ComplexOrder
open Matrix
namespace MinimaxProfile

variable {a b K : ℕ}

noncomputable def overlap {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
  (Extraction.bellProjector (d := Fin K) * Extraction.krausApply A
    ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
      (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re

theorem overlap_real_smul {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (c : ℝ) :
    overlap A U (c • X) = c * overlap A U X := by
  simp only [overlap, Matrix.mul_smul, Matrix.smul_mul,
    Extraction.krausApply_real_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem overlap_sum {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    overlap A U (∑ i, X i) = ∑ i, overlap A U (X i) := by
  simp only [overlap, Extraction.krausApply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_comm

/-- The adversarial ensemble is constructed from actual density matrices. -/
noncomputable def finiteAverage {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ := ∑ i, p i • X i

theorem finiteAverage_density {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hX : ∀ i, APPT.Quantum.IsDensity (X i)) :
    APPT.Quantum.IsDensity (finiteAverage p X) := by
  constructor
  · exact Matrix.posSemidef_sum Finset.univ (fun i _ => (hX i).1.smul (hp i))
  · simp only [finiteAverage, Matrix.trace_sum, Matrix.trace_smul, (hX _).2]
    rw [← Finset.sum_smul, hpsum, one_smul]

theorem overlap_finiteAverage {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (p : ι → ℝ) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    overlap A U (finiteAverage p X) = ∑ i, p i * overlap A U (X i) := by
  rw [finiteAverage, overlap_sum]
  simp only [overlap_real_smul]

/-- A guarantee for every input is bounded by its actual ensemble average. -/
theorem guarantee_le_average {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (p : ι → ℝ) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (c : ℝ)
    (hc : ∀ i, c ≤ overlap A U (X i)) :
    c ≤ overlap A U (finiteAverage p X) := by
  rw [overlap_finiteAverage]
  calc
    c = (∑ i, p i) * c := by rw [hpsum, one_mul]
    _ = ∑ i, p i * c := Finset.sum_mul _ _ _
    _ ≤ ∑ i, p i * overlap A U (X i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (hp i)

/-- Actual finite ensemble converse, simultaneously for every preprocessing
unitary and every complete Kraus channel with positive transpose conjugate. -/
theorem physical_finite_ensemble_bound {κ ι : Type*} [Fintype κ] [Fintype ι]
    (hK : 0 < K)
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
    (p : ι → ℝ) (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hX : ∀ i, APPT.Quantum.IsDensity (X i)) (c : ℝ)
    (hc : ∀ i, c ≤ overlap A U (X i)) :
    c ≤ min 1 (min ((a : ℝ) / K)
      (Real.sqrt (((finiteAverage p X) * (finiteAverage p X)).trace.re *
        ((a * b : ℝ) / (K : ℝ)^2)))) := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have h := ExtractionLocalCap.kraus_target_overlap_full_envelope A hA hpt
    (finiteAverage p X) (finiteAverage_density p X hp hpsum hX) U
  apply (guarantee_le_average A U p X hp hpsum c hc).trans
  simpa only [overlap, Fintype.card_fin] using h

end MinimaxProfile
