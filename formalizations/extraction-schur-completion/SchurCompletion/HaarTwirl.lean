import SchurCompletion.SchurWeylCentralizers
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum

noncomputable section

def tensorConjugate (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (U : OneCopyUnitary D) : Matrix (Word D k) (Word D k) ℂ :=
  tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k * A *
    (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ

theorem continuous_tensorConjugate (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    Continuous (tensorConjugate D k A) := by
  unfold tensorConjugate tensorMatrix
  apply continuous_pi
  intro w
  apply continuous_pi
  intro v
  change Continuous (fun U : OneCopyUnitary D =>
    ∑ j : Word D k, (∑ i : Word D k, (∏ t, (U : Matrix (Fin D) (Fin D) ℂ) (w t) (i t)) * A i j) *
      star (∏ t, (U : Matrix (Fin D) (Fin D) ℂ) (v t) (j t)))
  have hentry (i j : Fin D) : Continuous (fun U : OneCopyUnitary D =>
      (U : Matrix (Fin D) (Fin D) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul
  · apply continuous_finset_sum
    intro i _
    apply Continuous.mul
    · exact continuous_finset_prod _ (fun t _ => hentry (w t) (i t))
    · exact continuous_const
  · exact (continuous_finset_prod _ (fun t _ => hentry (v t) (j t))).star

theorem integrable_tensorConjugate (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    Integrable (tensorConjugate D k A) (unitaryHaar D) :=
  (continuous_tensorConjugate D k A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Literal Haar twirling of an arbitrary actual tensor-space matrix. -/
def haarTwirl (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    Matrix (Word D k) (Word D k) ℂ := ∫ U, tensorConjugate D k A U ∂unitaryHaar D

theorem haarOrbitAverage_eq_haarTwirl (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    haarOrbitAverage D k X = haarTwirl D k (tensorMatrix X k) := by
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [orbitTensor,tensorConjugate,tensorMatrix_mul,tensorMatrix_conjTranspose]

theorem tensorConjugate_mul (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (V U : OneCopyUnitary D) :
    tensorConjugate D k A (V*U) = tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k *
      tensorConjugate D k A U * (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ := by
  simp only [tensorConjugate,Matrix.UnitaryGroup.mul_val,tensorMatrix_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem haarTwirl_unitary_invariant (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (V : OneCopyUnitary D) :
    tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * haarTwirl D k A *
      (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ = haarTwirl D k A := by
  calc
    _ = ∫ U, tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * tensorConjugate D k A U *
        (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ ∂unitaryHaar D :=
      ((conjugateLinear _).toContinuousLinearMap.integral_comp_comm
        (integrable_tensorConjugate D k A)).symm
    _ = ∫ U, tensorConjugate D k A (V*U) ∂unitaryHaar D := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact (tensorConjugate_mul D k A V U).symm
    _ = _ := integral_mul_left_eq_self _ _

theorem haarTwirl_commutes (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (V : OneCopyUnitary D) :
    tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k * haarTwirl D k A =
      haarTwirl D k A * tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k := by
  have hV : (tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)ᴴ *
      tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k = 1 := (tensorUnitary V k).prop.1
  have h := congrArg (fun Y => Y * tensorMatrix (V : Matrix (Fin D) (Fin D) ℂ) k)
    (haarTwirl_unitary_invariant D k A V)
  simpa only [Matrix.mul_assoc,hV,Matrix.mul_one] using h

theorem haarTwirl_mem_permutationSpan (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k A ∈ permutationSpan D k := by
  apply (mem_permutationSpan_iff_commutes_unitaryTensor D k _).mpr
  intro U
  exact (haarTwirl_commutes D k A U).symm

theorem haarTwirl_eq_self_of_mem (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (hA : A ∈ permutationSpan D k) : haarTwirl D k A = A := by
  have hComm := (mem_permutationSpan_iff_commutes_unitaryTensor D k A).mp hA
  have hConst (U : OneCopyUnitary D) : tensorConjugate D k A U = A := by
    have hU : tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k *
        (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ = 1 := (tensorUnitary U k).prop.2
    rw [tensorConjugate,← hComm U,Matrix.mul_assoc,hU,Matrix.mul_one]
  simp only [haarTwirl,hConst,integral_const,probReal_univ,one_smul]

theorem haarTwirl_idempotent (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k (haarTwirl D k A) = haarTwirl D k A :=
  haarTwirl_eq_self_of_mem D k _ (haarTwirl_mem_permutationSpan D k A)

theorem haarTwirl_traceLeft (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ) :
    (B * haarTwirl D k A).trace =
      ∫ U, (B * tensorConjugate D k A U).trace ∂unitaryHaar D :=
  ((traceLeftLinear B).toContinuousLinearMap.integral_comp_comm
    (integrable_tensorConjugate D k A)).symm

theorem tensorConjugate_pairing (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ)
    (hB : B ∈ permutationSpan D k) (U : OneCopyUnitary D) :
    (B * tensorConjugate D k A U).trace = (B*A).trace := by
  have hComm := (mem_permutationSpan_iff_commutes_unitaryTensor D k B).mp hB U
  have hU : (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ *
      tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k = 1 := (tensorUnitary U k).prop.1
  unfold tensorConjugate
  calc
    _ = ((B*tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)*A*
        (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = ((tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k*B)*A*
        (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ).trace := by rw [hComm]
    _ = _ := by
      rw [Matrix.trace_mul_cycle]
      simp only [← Matrix.mul_assoc,hU,Matrix.one_mul]

/-- The actual Haar twirl is the trace-compatible projection onto the actual
permutation algebra, including dimensions where the permutation matrices
are linearly dependent. -/
theorem haarTwirl_pairing (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ)
    (hB : B ∈ permutationSpan D k) :
    (B * haarTwirl D k A).trace = (B*A).trace := by
  rw [haarTwirl_traceLeft]
  simp only [tensorConjugate_pairing D k A B hB,integral_const,probReal_univ,one_smul]

theorem haarTwirl_trace (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    (haarTwirl D k A).trace = A.trace := by
  simpa only [Matrix.one_mul] using haarTwirl_pairing D k A 1 (permutationSpan_one D k)

theorem haarTwirl_unique (D k : ℕ) (A C : Matrix (Word D k) (Word D k) ℂ)
    (hC : C ∈ permutationSpan D k)
    (hPair : ∀ B ∈ permutationSpan D k, (Bᴴ*C).trace = (Bᴴ*A).trace) :
    C = haarTwirl D k A := by
  let Z := C-haarTwirl D k A
  have hZ : Z ∈ permutationSpan D k := Submodule.sub_mem _ hC (haarTwirl_mem_permutationSpan D k A)
  have ht : (Zᴴ*Z).trace = 0 := by
    simp only [Z,Matrix.mul_sub,Matrix.trace_sub]
    rw [hPair _ hZ,haarTwirl_pairing D k A _ (permutationSpan_star_mem D k hZ),sub_self]
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

end
end ExtractionSchur
