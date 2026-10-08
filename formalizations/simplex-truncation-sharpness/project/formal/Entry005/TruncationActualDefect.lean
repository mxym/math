import Entry005.TruncationFacetFormula
import Entry005.TruncationCenteredHalfspaces
import Entry005.TruncationFacetVectors
import Entry005.TruncationRationalDefect
import Entry005.TruncationFacetDeterminants
import Entry005.TruncationScalarCancellation

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def facetLiftTranslationShear {d : ℕ} (z : Space d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun k => -z k) j)
    (fun l => Fin.cases 0 (fun k => if l = k then 1 else 0) j) i

theorem facet_lift_translation_shear_det {d : ℕ} (z : Space d) :
    (facetLiftTranslationShear z).det = 1 := by
  classical
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have hzero : facetLiftTranslationShear z 0 0 = 1 := rfl
    rw [hzero, one_mul]
    have he : (facetLiftTranslationShear z).submatrix Fin.succ Fin.succ = 1 := by
      ext i j
      simp [facetLiftTranslationShear, Matrix.submatrix_apply, Matrix.one_apply]
    rw [he, Matrix.det_one]
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
    simp [facetLiftTranslationShear]
  · simp

/-- Translation is an actual determinant-one row shear even when the raw
support numbers before translation are negative. No probability interpretation
of those signed support numbers is used. -/
theorem finite_facet_lifted_sample_translation {ι : Type*} {d : ℕ}
    (a h : ι → ℝ) (n : ι → Space d) (z : Space d) (b : Fin (d + 1) → ι) :
    (sampledMatrix (fun i j => a i *
      finiteFacetLift (fun k => h k - inner ℝ (n k) z) (fun i k => n i k) i j) b).det =
    (sampledMatrix (fun i j => a i * finiteFacetLift h (fun i k => n i k) i j) b).det := by
  classical
  let A := sampledMatrix (fun i j => a i * finiteFacetLift h (fun i k => n i k) i j) b
  have hm : sampledMatrix (fun i j => a i *
      finiteFacetLift (fun k => h k - inner ℝ (n k) z) (fun i k => n i k) i j) b =
        facetLiftTranslationShear z * A := by
    ext i j
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [facetLiftTranslationShear, sampledMatrix, Matrix.of_apply,
        finiteFacetLift, Fin.cases_zero, Fin.cases_succ, one_mul, A]
      rw [space_inner_eq_raw_dot]
      unfold dotProduct
      have hs : (∑ k : Fin d, -z k * (a (b j) * n (b j) k)) =
          -a (b j) * ∑ k : Fin d, n (b j) k * z k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hs]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, facetLiftTranslationShear,
        A, sampledMatrix, finiteFacetLift, Finset.sum_ite_eq]
  rw [hm, Matrix.det_mul, facet_lift_translation_shear_det, one_mul]

theorem finite_facet_lifted_tuple_translation {ι : Type*} [Fintype ι] {d : ℕ}
    (a h : ι → ℝ) (n : ι → Space d) (z : Space d) :
    (∑ b : Fin (d + 1) → ι,
      |(sampledMatrix (fun i j => a i *
        finiteFacetLift (fun k => h k - inner ℝ (n k) z) (fun i k => n i k) i j) b).det|) =
    ∑ b : Fin (d + 1) → ι,
      |(sampledMatrix (fun i j => a i * finiteFacetLift h (fun i k => n i k) i j) b).det| := by
  apply Finset.sum_congr rfl
  intro b _
  rw [finite_facet_lifted_sample_translation]

theorem truncation_centered_horizontal_tuple {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    actualFacetHorizontalTupleSum (truncationFacetNormal d) (truncationCenteredHeight d t) =
      ∑ b : Fin d → TruncationFacetIndex d,
        |horizontalDeterminant (fun j k => truncationRawHorizontal d t (b j) k)| := by
  unfold actualFacetHorizontalTupleSum
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext j k
  rw [truncation_centered_area_eq (by omega) t]
  exact truncation_actual_horizontal_row hd t ht0 ht1 (b j) k

theorem truncation_centered_lifted_tuple {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    actualFacetLiftedTupleSum (truncationFacetNormal d) (truncationCenteredHeight d t) =
      ∑ b : Fin (d + 1) → TruncationFacetIndex d,
        |(sampledMatrix (truncationRawLifted d t) b).det| := by
  unfold actualFacetLiftedTupleSum
  have ha : finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationCenteredHeight d t) =
      finiteHalfspaceFacetArea (truncationFacetNormal d) (truncationFacetHeight d t) := by
    funext i
    exact truncation_centered_area_eq (by omega) t i
  rw [ha]
  change (∑ b : Fin (d + 1) → TruncationFacetIndex d,
      |(sampledMatrix (fun i j => finiteHalfspaceFacetArea (truncationFacetNormal d)
        (truncationFacetHeight d t) i * finiteFacetLift
        (fun k => truncationFacetHeight d t k - inner ℝ (truncationFacetNormal d k) (truncationCenter d t))
        (fun i k => truncationFacetNormal d i k) i j) b).det|) = _
  rw [finite_facet_lifted_tuple_translation]
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  ext i j
  exact truncation_actual_lifted_row hd t ht0 ht1 (b j) i

/-- The actual canonical geometric invariant expressed using the proved raw
facet vectors of the real truncated simplex. All geometry is discharged; only
the finite determinant sums on the right remain to be evaluated. -/
theorem truncation_actual_defect_raw_facet_formula {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    entryDefect (truncationSet d t) =
      (∑ b : Fin (d + 1) → TruncationFacetIndex d,
        |(sampledMatrix (truncationRawLifted d t) b).det|) /
      ((d + 1 : ℝ) * (d : ℝ) * ((1 - t ^ d) / (d.factorial : ℝ)) *
        (∑ b : Fin d → TruncationFacetIndex d,
          |horizontalDeterminant (fun j k => truncationRawHorizontal d t (b j) k)|)) -
      1 / (d + 1 : ℝ) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have he := finite_halfspace_entryA_actual_facet_tuple_ratio
    (truncationFacetNormal d) (truncationCenteredHeight d t)
    (truncation_facet_norm (by omega)) (truncation_centered_height_pos (by omega) t ht0 ht1)
    (truncation_facet_normal_injective hd) (truncation_centered_compact (by omega) t ht0 ht1)
  rw [truncation_centered_entryA (by omega) t,
    truncation_centered_horizontal_tuple hd t ht0 ht1,
    truncation_centered_lifted_tuple hd t ht0 ht1,
    truncation_centered_volume (by omega) t,
    truncation_actual_volume (by omega) t ht0.le ht1.le] at he
  unfold entryDefect
  rw [he]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  ring

def truncationPackedIndex (d : ℕ) : TruncationFacetIndex d ≃ Fin (d + 2) where
  toFun
    | Sum.inl i => i.succ.succ
    | Sum.inr false => 0
    | Sum.inr true => 1
  invFun := Fin.cases (Sum.inr false) (Fin.cases (Sum.inr true) Sum.inl)
  left_inv i := by
    cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
  right_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl

theorem truncation_raw_tuple_reindex {d k : ℕ}
    (v : TruncationFacetIndex d → Fin k → ℝ) :
    (∑ b : Fin k → TruncationFacetIndex d, |horizontalDeterminant (fun j => v (b j))|) =
    ∑ b : Fin k → Fin (d + 2),
      |horizontalDeterminant (fun j => v ((truncationPackedIndex d).symm (b j)))| := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin k => truncationPackedIndex d))
  intro b
  simp

theorem truncation_raw_horizontal_packed (d : ℕ) (t : ℝ) :
    (fun i j => truncationRawHorizontal d t ((truncationPackedIndex d).symm i) j) =
      truncationPackedHorizontal d (truncationFacetScale d)
        (1 - t ^ (d - 1)) (t ^ (d - 1)) := by
  funext i j
  induction i using Fin.cases with
  | zero => simp [truncationPackedIndex, truncationRawHorizontal,
      truncationPackedHorizontal, truncationDiagonal]
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      change ((-truncationFacetScale d * t ^ (d - 1)) • truncationDiagonal d) j =
        -truncationFacetScale d * t ^ (d - 1)
      simp [truncationDiagonal]
    | succ i =>
      simp [truncationPackedIndex, truncationRawHorizontal,
        truncationPackedHorizontal, truncationCoordinateVector, truncationVertex_apply]
      split_ifs <;> simp

theorem truncation_raw_lifted_packed (d : ℕ) (t : ℝ) :
    (fun i => truncationRawLifted d t ((truncationPackedIndex d).symm i)) =
      truncationPackedLifted d (truncationFacetScale d)
        (1 - t ^ (d - 1)) (t ^ (d - 1)) (t ^ d) := by
  funext i j
  induction j using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => induction i using Fin.cases <;> rfl
  | succ j =>
    have he := congrFun (congrFun (truncation_raw_horizontal_packed d t) i) j
    induction i using Fin.cases with
    | zero => exact he
    | succ i => induction i using Fin.cases <;> exact he

theorem truncation_raw_horizontal_tuple_sum {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (∑ b : Fin d → TruncationFacetIndex d,
      |horizontalDeterminant (fun j k => truncationRawHorizontal d t (b j) k)|) =
      (d.factorial : ℝ) * (truncationFacetScale d) ^ d *
        ((1 - t ^ (d - 1)) ^ d + (d : ℝ) * (1 + t ^ (d - 1)) *
          (1 - t ^ (d - 1)) ^ (d - 1)) := by
  rw [truncation_raw_tuple_reindex (fun i j => truncationRawHorizontal d t i j)]
  change truncationPackedTupleSum
    (fun i j => truncationRawHorizontal d t ((truncationPackedIndex d).symm i) j) = _
  rw [truncation_raw_horizontal_packed]
  apply truncation_packed_horizontal_tuple_sum hd
  · unfold truncationFacetScale
    positivity
  · exact sub_nonneg.mpr (pow_le_one₀ ht0.le ht1.le)
  · positivity

theorem truncation_raw_lifted_tuple_sum {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (∑ b : Fin (d + 1) → TruncationFacetIndex d,
      |(sampledMatrix (truncationRawLifted d t) b).det|) =
      ((d + 1).factorial : ℝ) * (truncationFacetScale d) ^ (d + 1) *
        ((1 - t ^ (d - 1)) ^ d * (1 + t ^ d) +
          (d : ℝ) * (1 - t ^ (d - 1)) ^ (d - 1) * (t ^ (d - 1) - t ^ d)) := by
  change (∑ b : Fin (d + 1) → TruncationFacetIndex d,
    |horizontalDeterminant (fun j => truncationRawLifted d t (b j))|) = _
  rw [truncation_raw_tuple_reindex (truncationRawLifted d t)]
  change truncationPackedTupleSum
    (fun i => truncationRawLifted d t ((truncationPackedIndex d).symm i)) = _
  rw [truncation_raw_lifted_packed]
  apply truncation_packed_lifted_tuple_sum (by omega)
  · unfold truncationFacetScale
    positivity
  · exact sub_nonneg.mpr (pow_le_one₀ ht0.le ht1.le)
  · positivity
  · have hp : t ^ d = t ^ (d - 1) * t := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hp]
    exact mul_le_of_le_one_right (pow_nonneg ht0.le _) ht1.le

/-- Equation (D) for the actual geometric defect of the literal truncation.
All facets, intrinsic areas, volume, projection-body/pyramid dependencies and
the finite determinant sums are proved; no geometric identity is a premise. -/
theorem truncation_entryDefect_exact {d : ℕ} (hd : 2 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    entryDefect (truncationSet d t) = truncationRationalDefect d t := by
  rw [truncation_actual_defect_raw_facet_formula hd t ht0 ht1,
    truncation_raw_lifted_tuple_sum hd t ht0 ht1,
    truncation_raw_horizontal_tuple_sum hd t ht0 ht1]
  exact truncation_scalar_cancellation hd ht0 ht1

end Entry005
