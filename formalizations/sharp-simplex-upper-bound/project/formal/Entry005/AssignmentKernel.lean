import Entry005.LargestCoordinate

/-! The largest-coordinate assignment error is linear in the finite witness cost.
`pairAssignmentCost` uses one half of the ordered pair sum, exactly the unordered
pair cost. No probabilistic assignment estimate is an input to this kernel.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def negativeAssignmentCost {n : ℕ} (a : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, min 1 (max (-a i) 0)

def pairAssignmentCost {n : ℕ} (a : Fin (n + 1) → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else min (max (a i) 0) (max (a j) 0)

def assignmentCost {n : ℕ} (a : Fin (n + 1) → ℝ) : ℝ :=
  negativeAssignmentCost a + pairAssignmentCost a

theorem truncated_nonneg_le {x L : ℝ} (hx : 0 ≤ x) (hxL : x ≤ L) (hL : 1 ≤ L) :
    x ≤ L * min 1 x := by
  rcases le_total 1 x with h | h
  · rw [min_eq_left h]; simpa using hxL
  · rw [min_eq_right h]; nlinarith

theorem positive_off_max_le_pair_cost {n : ℕ} (a : Fin (n + 1) → ℝ) :
    (∑ i, if i = largestCoordinate a then 0 else max (a i) 0) ≤ pairAssignmentCost a := by
  let r := largestCoordinate a
  let U : ℝ := ∑ i, if i = r then 0 else max (a i) 0
  have hpoint (i j : Fin (n + 1)) :
      (if i = r then (if j = r then 0 else max (a j) 0) else 0) +
        (if j = r then (if i = r then 0 else max (a i) 0) else 0) ≤
          if i = j then 0 else min (max (a i) 0) (max (a j) 0) := by
    have hi := max_le_max (largest_coordinate_max a i) (le_refl (0 : ℝ))
    have hj := max_le_max (largest_coordinate_max a j) (le_refl (0 : ℝ))
    change max (a i) 0 ≤ max (a r) 0 at hi
    change max (a j) 0 ≤ max (a r) 0 at hj
    by_cases hir : i = r
    · subst i
      by_cases hjr : j = r
      · subst j; simp
      · simp only [hjr, Ne.symm hjr, ite_true, ite_false, min_eq_right hj, add_zero]
        exact le_refl _
    · by_cases hjr : j = r
      · subst j
        simp only [hir, ite_true, ite_false, min_eq_left hi, zero_add]
        exact le_refl _
      · simp only [hir, hjr, ite_false, zero_add]
        split_ifs
        · exact le_refl 0
        · exact le_min (le_max_right _ _) (le_max_right _ _)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
  have hleft :
      (∑ i, ∑ j,
        ((if i = r then (if j = r then 0 else max (a j) 0) else 0) +
          (if j = r then (if i = r then 0 else max (a i) 0) else 0))) = 2 * U := by
    simp [U, Finset.sum_add_distrib, Finset.sum_ite_irrel, two_mul]
  rw [hleft] at hsum
  change U ≤ (1 / 2 : ℝ) * _
  linarith

theorem off_max_l1_le_cost {n : ℕ} {a : Fin (n + 1) → ℝ} {L : ℝ}
    (hL : 1 ≤ L) (ha : ∀ i, |a i| ≤ L) :
    (∑ i, if i = largestCoordinate a then 0 else |a i|) ≤ L * assignmentCost a := by
  have hneg : (∑ i, max (-a i) 0) ≤ L * negativeAssignmentCost a := by
    unfold negativeAssignmentCost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply truncated_nonneg_le (le_max_right _ _) _ hL
    exact max_le (by have h := (abs_le.1 (ha i)).1; linarith) (by linarith)
  have hpair := positive_off_max_le_pair_cost a
  have hpos : 0 ≤ pairAssignmentCost a := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact le_refl 0
    · exact le_min (le_max_right _ _) (le_max_right _ _)
  have hdecomp : (∑ i, if i = largestCoordinate a then 0 else |a i|) ≤
      (∑ i, max (-a i) 0) + (∑ i, if i = largestCoordinate a then 0 else max (a i) 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hir : i = largestCoordinate a
    · simp only [hir, ite_true, add_zero]; exact le_max_right _ _
    · simp only [hir, ite_false]; grind
  unfold assignmentCost
  nlinarith

theorem largest_coordinate_assignment_error {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {w : Fin (n + 1) → E} {x : E}
    {a : Fin (n + 1) → ℝ} {L : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ 1) (hsum : ∑ i, a i = 1)
    (hx : ∑ i, a i • w i = x) (hL : 1 ≤ L) (ha : ∀ i, |a i| ≤ L) :
    ‖x - w (largestCoordinate a)‖ ≤ 2 * L * assignmentCost a := by
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
  have hdist (i : Fin (n + 1)) : ‖w i - w r‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hw i, hw r])
  have hnorm (i : Fin (n + 1)) :
      ‖(if i = r then 0 else a i • (w i - w r))‖ ≤
        2 * (if i = r then 0 else |a i|) := by
    by_cases hir : i = r
    · simp [hir]
    · simp only [hir, ite_false, norm_smul, Real.norm_eq_abs]
      nlinarith [hdist i, abs_nonneg (a i)]
  calc
    ‖x - w (largestCoordinate a)‖ = ‖∑ i, if i = r then 0 else a i • (w i - w r)‖ := by
      rw [hide, hexp]
    _ ≤ ∑ i, ‖(if i = r then 0 else a i • (w i - w r))‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * (if i = r then 0 else |a i|) :=
      Finset.sum_le_sum fun i _ => hnorm i
    _ = 2 * ∑ i, if i = r then 0 else |a i| := by rw [Finset.mul_sum]
    _ ≤ 2 * (L * assignmentCost a) :=
      mul_le_mul_of_nonneg_left (off_max_l1_le_cost hL ha) (by norm_num)
    _ = 2 * L * assignmentCost a := by ring

theorem assignment_cost_nonneg {n : ℕ} (a : Fin (n + 1) → ℝ) :
    0 ≤ assignmentCost a := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun i _ => le_min (by norm_num) (le_max_right _ _)
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact le_refl 0
    · exact le_min (le_max_right _ _) (le_max_right _ _)

theorem integrated_largest_assignment_error {n : ℕ} {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {w : Fin (n + 1) → E} {X : α → E}
    {a : α → Fin (n + 1) → ℝ} {L B : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ 1) (hX : Measurable X)
    (hma : ∀ i, Measurable (fun x => a x i)) (hL : 1 ≤ L)
    (hsum : ∀ᵐ x ∂μ, ∑ i, a x i = 1)
    (hx : ∀ᵐ x ∂μ, ∑ i, a x i • w i = X x)
    (ha : ∀ᵐ x ∂μ, ∀ i, |a x i| ≤ L)
    (hcost : Integrable (fun x => assignmentCost (a x)) μ)
    (hbudget : (∫ x, assignmentCost (a x) ∂μ) ≤ B) :
    Measurable (fun x => largestCoordinate (a x)) ∧
      Integrable (fun x => ‖X x - w (largestCoordinate (a x))‖) μ ∧
      (∫ x, ‖X x - w (largestCoordinate (a x))‖ ∂μ) ≤ 2 * L * B := by
  have hr := measurable_largest_coordinate hma
  have hwsel : Measurable (fun x => w (largestCoordinate (a x))) :=
    (measurable_of_finite w).comp hr
  have hbound : ∀ᵐ x ∂μ, ‖X x - w (largestCoordinate (a x))‖ ≤
      (2 * L) * assignmentCost (a x) := by
    filter_upwards [hsum, hx, ha] with x hs hx ha
    exact largest_coordinate_assignment_error hw hs hx hL ha
  have hinterror : Integrable (fun x => ‖X x - w (largestCoordinate (a x))‖) μ :=
    (hcost.const_mul (2 * L)).mono' (hX.sub hwsel).norm.aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound)
  refine ⟨hr, hinterror, ?_⟩
  calc
    (∫ x, ‖X x - w (largestCoordinate (a x))‖ ∂μ) ≤
        ∫ x, (2 * L) * assignmentCost (a x) ∂μ :=
      integral_mono_ae hinterror (hcost.const_mul (2 * L)) hbound
    _ = (2 * L) * ∫ x, assignmentCost (a x) ∂μ := integral_const_mul _ _
    _ ≤ 2 * L * B := mul_le_mul_of_nonneg_left hbudget (by linarith)

end Entry005
