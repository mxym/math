import Entry005.IntegratedWitness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The actual lifted determinant and its centered-law cancellation identity.
Coordinates here use `Fin d → ℝ`; no abstract affine functional is substituted
for the determinant. The varying point occupies column zero.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def witnessMatrix {d : ℕ} (base : Fin d → Fin d → ℝ) (x : Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 1 x i)
    (fun k : Fin d => Fin.cases 1 (base k) i) j

def liftedDeterminant {d : ℕ} (base : Fin d → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  (witnessMatrix base x).det

def horizontalDeterminant {d : ℕ} (base : Fin d → Fin d → ℝ) : ℝ :=
  Matrix.det (Matrix.of fun i j => base j i)

def witnessCofactor {d : ℕ} (base : Fin d → Fin d → ℝ) (i : Fin (d + 1)) : ℝ :=
  (-1) ^ (i : ℕ) * ((witnessMatrix base 0).submatrix i.succAbove Fin.succ).det

theorem lifted_determinant_expansion {d : ℕ} (base : Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) :
    liftedDeterminant base x =
      horizontalDeterminant base + ∑ i : Fin d, witnessCofactor base i.succ * x i := by
  unfold liftedDeterminant
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hminor (i : Fin (d + 1)) :
      (witnessMatrix base x).submatrix i.succAbove Fin.succ =
        (witnessMatrix base 0).submatrix i.succAbove Fin.succ := by
    ext j k
    simp [witnessMatrix, Matrix.submatrix]
  simp only [hminor]
  simp [witnessMatrix, witnessCofactor, horizontalDeterminant,
    Matrix.submatrix, mul_assoc, mul_comm]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem measurable_lifted_determinant {d : ℕ} {base : α → Fin d → Fin d → ℝ}
    {X : α → Fin d → ℝ}
    (hbase : ∀ i j, Measurable (fun x => base x i j))
    (hX : ∀ i, Measurable (fun x => X x i)) :
    Measurable (fun x => liftedDeterminant (base x) (X x)) := by
  have hentry (i j : Fin (d + 1)) :
      Measurable (fun x => witnessMatrix (base x) (X x) i j) := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases <;> simp only [witnessMatrix, Fin.cases_zero, Fin.cases_succ]
      all_goals exact measurable_const
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa only [witnessMatrix, Fin.cases_zero, Fin.cases_succ] using hX i
      | succ j => simpa only [witnessMatrix, Fin.cases_succ] using hbase j i
  unfold liftedDeterminant
  simp only [Matrix.det_apply]
  apply Finset.measurable_sum
  intro p _
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i _
  exact hentry (p i) i

theorem lifted_determinant_integrable {d : ℕ} (base : Fin d → Fin d → ℝ)
    [IsFiniteMeasure μ] {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ) :
    Integrable (fun x => liftedDeterminant base (X x)) μ := by
  simp_rw [lifted_determinant_expansion]
  exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hX i).const_mul _)

theorem integral_lifted_determinant {d : ℕ} (base : Fin d → Fin d → ℝ)
    [IsProbabilityMeasure μ] {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0) :
    (∫ x, liftedDeterminant base (X x) ∂μ) = horizontalDeterminant base := by
  simp_rw [lifted_determinant_expansion]
  rw [integral_add (integrable_const _)
    (integrable_finsetSum _ fun i _ => (hX i).const_mul _),
    integral_finsetSum _ fun i _ => (hX i).const_mul _]
  simp [integral_const_mul, hcenter]

theorem centered_determinant_cancellation {d : ℕ} (base : Fin d → Fin d → ℝ)
    [IsProbabilityMeasure μ] {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0) :
    (∫ x, |liftedDeterminant base (X x)| ∂μ) - |horizontalDeterminant base| =
      2 * min (positiveIntegral μ (fun x => liftedDeterminant base (X x)))
        (negativeIntegral μ (fun x => liftedDeterminant base (X x))) := by
  have h := integral_cancellation_identity (lifted_determinant_integrable base hX)
  simpa [cancellationDefect, integral_lifted_determinant base hX hcenter] using h

theorem centered_determinant_witness_le {d : ℕ} (base : Fin d → Fin d → ℝ)
    [IsProbabilityMeasure μ] {X : α → Fin d → ℝ}
    (hX : ∀ i, Integrable (fun x => X x i) μ)
    (hcenter : ∀ i, (∫ x, X x i ∂μ) = 0) :
    (∫ z : α × α, oppositeWitness (liftedDeterminant base (X z.1))
        (liftedDeterminant base (X z.2)) ∂μ.prod μ) ≤
      (∫ x, |liftedDeterminant base (X x)| ∂μ) - |horizontalDeterminant base| := by
  have h := integrated_opposite_witness_le (lifted_determinant_integrable base hX)
  simpa [cancellationDefect, integral_lifted_determinant base hX hcenter] using h

end Entry005
