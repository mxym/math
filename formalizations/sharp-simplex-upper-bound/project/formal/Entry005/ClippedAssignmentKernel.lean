import Entry005.AssignmentKernel

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem off_max_l1_le_cost_of_no_clipping {n : ℕ} (a : Fin (n + 1) → ℝ)
    (hclip : ∀ i, max (-a i) 0 ≤ 1) :
    (∑ i, if i = largestCoordinate a then 0 else |a i|) ≤ assignmentCost a := by
  have hneg : (∑ i, max (-a i) 0) = negativeAssignmentCost a := by
    simp only [negativeAssignmentCost, min_eq_right (hclip _)]
  have hdecomp : (∑ i, if i = largestCoordinate a then 0 else |a i|) ≤
      (∑ i, max (-a i) 0) + (∑ i, if i = largestCoordinate a then 0 else max (a i) 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hir : i = largestCoordinate a
    · simp only [hir, ite_true, add_zero]; exact le_max_right _ _
    · simp only [hir, ite_false]; grind
  exact hdecomp.trans (by
    rw [hneg]
    exact add_le_add (le_refl _) (positive_off_max_le_pair_cost a))

/-- Clipping removes the coefficient bound entirely. The distance assumptions
are actual distances in any real normed space, so delta may be a support diameter. -/
theorem largest_coordinate_clipped_assignment_error {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {w : Fin (n + 1) → E} {x : E}
    {a : Fin (n + 1) → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hww : ∀ i j, ‖w i - w j‖ ≤ δ)
    (hxw : ∀ i, ‖x - w i‖ ≤ δ)
    (hsum : ∑ i, a i = 1) (hx : ∑ i, a i • w i = x) :
    ‖x - w (largestCoordinate a)‖ ≤ δ * assignmentCost a := by
  by_cases hclip : ∃ i, 1 ≤ max (-a i) 0
  · obtain ⟨i, hi⟩ := hclip
    have hneg : 1 ≤ negativeAssignmentCost a := by
      unfold negativeAssignmentCost
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        le_min (by norm_num : (0 : ℝ) ≤ 1) (le_max_right (-a j) 0))
        (Finset.mem_univ i)
      simpa only [min_eq_left hi] using h
    have hp : 0 ≤ pairAssignmentCost a := by
      unfold pairAssignmentCost
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro j _
      apply Finset.sum_nonneg
      intro k _
      split_ifs
      · exact le_refl 0
      · exact le_min (le_max_right _ _) (le_max_right _ _)
    have hc : 1 ≤ assignmentCost a := by unfold assignmentCost; linarith
    exact (hxw _).trans (by nlinarith)
  · have hnoclip : ∀ i, max (-a i) 0 ≤ 1 := by
      intro i
      exact (lt_of_not_ge (fun hi => hclip ⟨i, hi⟩)).le
    let r := largestCoordinate a
    have hexp : (∑ i, a i • (w i - w r)) = x - w r := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, hx, ← Finset.sum_smul, hsum, one_smul]
    have hide : (∑ i, if i = r then 0 else a i • (w i - w r)) =
        ∑ i, a i • (w i - w r) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hir : i = r
      · subst i; simp
      · simp [hir]
    have hnorm (i : Fin (n + 1)) :
        ‖(if i = r then 0 else a i • (w i - w r))‖ ≤
          δ * (if i = r then 0 else |a i|) := by
      by_cases hir : i = r
      · simp [hir]
      · simp only [hir, ite_false, norm_smul, Real.norm_eq_abs]
        nlinarith [hww i r, abs_nonneg (a i)]
    calc
      ‖x - w (largestCoordinate a)‖ = ‖∑ i, if i = r then 0 else a i • (w i - w r)‖ := by
        rw [hide, hexp]
      _ ≤ ∑ i, ‖(if i = r then 0 else a i • (w i - w r))‖ := norm_sum_le _ _
      _ ≤ ∑ i, δ * (if i = r then 0 else |a i|) := Finset.sum_le_sum fun i _ => hnorm i
      _ = δ * ∑ i, if i = r then 0 else |a i| := by rw [Finset.mul_sum]
      _ ≤ δ * assignmentCost a :=
        mul_le_mul_of_nonneg_left (off_max_l1_le_cost_of_no_clipping a hnoclip) hδ

theorem unit_ball_clipped_assignment_error {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {w : Fin (n + 1) → E} {x : E}
    {a : Fin (n + 1) → ℝ}
    (hw : ∀ i, ‖w i‖ ≤ 1) (hball : ‖x‖ ≤ 1)
    (hsum : ∑ i, a i = 1) (hx : ∑ i, a i • w i = x) :
    ‖x - w (largestCoordinate a)‖ ≤ 2 * assignmentCost a := by
  apply largest_coordinate_clipped_assignment_error (by norm_num) _ _ hsum hx
  · intro i j
    exact (norm_sub_le _ _).trans (by linarith [hw i, hw j])
  · intro i
    exact (norm_sub_le _ _).trans (by linarith [hw i])

theorem integrated_clipped_largest_assignment_error {n : ℕ} {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {w : Fin (n + 1) → E} {X : α → E}
    {a : α → Fin (n + 1) → ℝ} {δ B : ℝ}
    (hδ : 0 ≤ δ) (hww : ∀ i j, ‖w i - w j‖ ≤ δ)
    (hxw : ∀ᵐ x ∂μ, ∀ i, ‖X x - w i‖ ≤ δ)
    (hX : Measurable X) (hma : ∀ i, Measurable (fun x => a x i))
    (hsum : ∀ᵐ x ∂μ, ∑ i, a x i = 1)
    (hx : ∀ᵐ x ∂μ, ∑ i, a x i • w i = X x)
    (hcost : Integrable (fun x => assignmentCost (a x)) μ)
    (hbudget : (∫ x, assignmentCost (a x) ∂μ) ≤ B) :
    Measurable (fun x => largestCoordinate (a x)) ∧
      Integrable (fun x => ‖X x - w (largestCoordinate (a x))‖) μ ∧
      (∫ x, ‖X x - w (largestCoordinate (a x))‖ ∂μ) ≤ δ * B := by
  have hr := measurable_largest_coordinate hma
  have hwsel : Measurable (fun x => w (largestCoordinate (a x))) :=
    (measurable_of_finite w).comp hr
  have hbound : ∀ᵐ x ∂μ, ‖X x - w (largestCoordinate (a x))‖ ≤
      δ * assignmentCost (a x) := by
    filter_upwards [hxw, hsum, hx] with x hxw hs hx
    exact largest_coordinate_clipped_assignment_error hδ hww hxw hs hx
  have hi : Integrable (fun x => ‖X x - w (largestCoordinate (a x))‖) μ :=
    (hcost.const_mul δ).mono' (hX.sub hwsel).norm.aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound)
  refine ⟨hr, hi, ?_⟩
  calc
    (∫ x, ‖X x - w (largestCoordinate (a x))‖ ∂μ) ≤
        ∫ x, δ * assignmentCost (a x) ∂μ :=
      integral_mono_ae hi (hcost.const_mul δ) hbound
    _ = δ * ∫ x, assignmentCost (a x) ∂μ := integral_const_mul _ _
    _ ≤ δ * B := mul_le_mul_of_nonneg_left hbudget hδ

end Entry005
