import Entry005.DeterminantMoment
import Entry005.AssignmentKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace Entry005

def anchorMatrix {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  witnessMatrix (fun i => w i.succ) (w 0)

def anchorCoordinates {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    Fin (d + 1) → ℝ := (anchorMatrix w)⁻¹ *ᵥ liftedCoordinates id x

def replacementDeterminant {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (x : Fin d → ℝ) (i : Fin (d + 1)) : ℝ :=
  ((anchorMatrix w).updateCol i (liftedCoordinates id x)).det

theorem anchor_matrix_entry {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ) (i j) :
    anchorMatrix w i j = Fin.cases 1 (w j) i := by
  induction j using Fin.cases <;> rfl

theorem anchor_matrix_mul_coordinates {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) :
    anchorMatrix w *ᵥ anchorCoordinates w x = liftedCoordinates id x := by
  unfold anchorCoordinates
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

theorem anchor_coordinates_sum {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) :
    ∑ i, anchorCoordinates w x i = 1 := by
  have h := congrFun (anchor_matrix_mul_coordinates w hdet x) 0
  simpa [Matrix.mulVec, dotProduct, anchor_matrix_entry, liftedCoordinates] using h

theorem anchor_coordinates_reconstruct {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) :
    ∑ i, anchorCoordinates w x i • w i = x := by
  ext k
  have h := congrFun (anchor_matrix_mul_coordinates w hdet x) k.succ
  simpa [Matrix.mulVec, dotProduct, anchor_matrix_entry, liftedCoordinates,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem replacement_determinant_coordinates {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0)
    (x : Fin d → ℝ) (i : Fin (d + 1)) :
    replacementDeterminant w x i = (anchorMatrix w).det * anchorCoordinates w x i := by
  have h := congrFun ((anchorMatrix w).det_smul_inv_mulVec_eq_cramer
    (liftedCoordinates id x) (isUnit_iff_ne_zero.mpr hdet)) i
  simpa [replacementDeterminant, anchorCoordinates, Matrix.cramer_apply,
    Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] using h.symm

theorem measurable_anchor_coordinates {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ) (i) :
    Measurable (fun x => anchorCoordinates w x i) := by
  unfold anchorCoordinates Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j _
  apply Measurable.const_mul
  induction j using Fin.cases with
  | zero => simp [liftedCoordinates]
  | succ k =>
    simpa [liftedCoordinates] using (measurable_pi_apply k : Measurable (fun x : Fin d → ℝ => x k))

theorem opposite_witness_neg_neg (a b : ℝ) :
    oppositeWitness (-a) (-b) = oppositeWitness a b := by
  simp [oppositeWitness, add_comm]

theorem opposite_witness_mul_nonneg {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) :
    oppositeWitness (c * a) (c * b) = c * oppositeWitness a b := by
  have hmax (t : ℝ) : max (c * t) 0 = c * max t 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg t 0 hc).symm
  have hmin (s t : ℝ) : min (c * s) (c * t) = c * min s t :=
    (mul_min_of_nonneg s t hc).symm
  simp only [oppositeWitness, ← mul_neg, hmax, hmin, mul_add]

theorem opposite_witness_mul (c a b : ℝ) :
    oppositeWitness (c * a) (c * b) = |c| * oppositeWitness a b := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, opposite_witness_mul_nonneg hc]
  · calc
      oppositeWitness (c * a) (c * b) = oppositeWitness ((-c) * a) ((-c) * b) := by
        simpa only [neg_mul] using (opposite_witness_neg_neg (c * a) (c * b)).symm
      _ = (-c) * oppositeWitness a b := opposite_witness_mul_nonneg (neg_nonneg.mpr hc) a b
      _ = |c| * oppositeWitness a b := by rw [abs_of_nonpos hc]

theorem first_replacement_witness {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) (i) :
    oppositeWitness (anchorMatrix w).det (replacementDeterminant w x i) =
      |(anchorMatrix w).det| * min 1 (max (-anchorCoordinates w x i) 0) := by
  rw [replacement_determinant_coordinates w hdet]
  conv_lhs => arg 1; rw [← mul_one (anchorMatrix w).det]
  rw [opposite_witness_mul]
  congr 1
  simp [oppositeWitness]

theorem pair_replacement_witness_lower {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) (i j) :
    |(anchorMatrix w).det| * min (max (anchorCoordinates w x i) 0)
      (max (anchorCoordinates w x j) 0) ≤
      oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j) := by
  rw [replacement_determinant_coordinates w hdet, replacement_determinant_coordinates w hdet,
    ← mul_neg, opposite_witness_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold oppositeWitness
  simp only [neg_neg]
  exact le_add_of_nonneg_right (le_min (le_max_right _ _) (le_max_right _ _))

def determinantAssignmentWitness {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (∑ i, oppositeWitness (anchorMatrix w).det (replacementDeterminant w x i)) +
    (1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else
      oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j)

theorem actual_determinant_assignment_cost {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0) (x : Fin d → ℝ) :
    |(anchorMatrix w).det| * assignmentCost (anchorCoordinates w x) ≤
      determinantAssignmentWitness w x := by
  have hp : ∀ i j : Fin (d + 1),
      |(anchorMatrix w).det| * (if i = j then 0 else
        min (max (anchorCoordinates w x i) 0) (max (anchorCoordinates w x j) 0)) ≤
      if i = j then 0 else
        oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j) := by
    intro i j
    split_ifs with h
    · simp
    · exact pair_replacement_witness_lower w hdet x i j
  have hsum : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      |(anchorMatrix w).det| * (if i = j then 0 else
        min (max (anchorCoordinates w x i) 0) (max (anchorCoordinates w x j) 0))) ≤
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), if i = j then 0 else
        oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
  unfold assignmentCost negativeAssignmentCost pairAssignmentCost determinantAssignmentWitness
  simp_rw [first_replacement_witness w hdet]
  rw [mul_add]
  apply add_le_add
  · rw [Finset.mul_sum]
  · have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp only [← Finset.mul_sum] at hscaled
    convert hscaled using 1; ring

theorem integrable_anchor_coordinates {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (i) :
    Integrable (fun x => anchorCoordinates w x i) ν := by
  unfold anchorCoordinates Matrix.mulVec dotProduct
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  induction j using Fin.cases with
  | zero => simp [liftedCoordinates]
  | succ k => simpa [liftedCoordinates] using hX k

theorem assignment_cost_integrable {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (a : α → Fin (n + 1) → ℝ)
    (ha : ∀ i, Integrable (fun x => a x i) μ) :
    Integrable (fun x => assignmentCost (a x)) μ := by
  unfold assignmentCost negativeAssignmentCost pairAssignmentCost
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    exact (integrable_const (1 : ℝ)).inf (ha i).neg_part
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    by_cases h : i = j
    · simp [h]
    · simp only [h, ite_false]
      exact (ha i).pos_part.inf (ha j).pos_part

theorem opposite_witness_integrable_same {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => oppositeWitness (f x) (g x)) μ := by
  exact (hf.pos_part.inf hg.neg_part).add (hf.neg_part.inf hg.pos_part)

theorem determinant_assignment_witness_integrable {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0) :
    Integrable (determinantAssignmentWitness w) ν := by
  have hr (i) : Integrable (fun x => replacementDeterminant w x i) ν := by
    simp_rw [replacement_determinant_coordinates w hdet]
    exact (integrable_anchor_coordinates ν hX w i).const_mul _
  unfold determinantAssignmentWitness
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    exact opposite_witness_integrable_same (integrable_const _) (hr i)
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    by_cases h : i = j
    · simp [h]
    · simpa only [h, ite_false, Pi.neg_apply] using opposite_witness_integrable_same (hr i) (hr j).neg

theorem integrated_actual_determinant_assignment_cost {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (hdet : (anchorMatrix w).det ≠ 0) :
    (∫ x, assignmentCost (anchorCoordinates w x) ∂ν) ≤
      (∫ x, determinantAssignmentWitness w x ∂ν) / |(anchorMatrix w).det| := by
  apply (le_div_iff₀ (abs_pos.mpr hdet)).2
  rw [mul_comm, ← integral_const_mul]
  apply integral_mono
  · exact (assignment_cost_integrable ν (anchorCoordinates w)
      (integrable_anchor_coordinates ν hX w)).const_mul _
  · exact determinant_assignment_witness_integrable ν hX w hdet
  · exact actual_determinant_assignment_cost w hdet

end Entry005
