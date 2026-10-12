import Entry005.ActualBodyPolarBoundary

/-! Actual support-height assignment tests and exact finite-facet integral
formulas. These statements do not assert a volume derivative or a Minkowski
inequality. Every limit statement uses its supplied actual compact law. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Entry005

section SupportTest

variable {d : ℕ}

theorem compact_support_height_mono
    (K P : Set (Space d)) (hcK : IsCompact K) (hneK : K.Nonempty)
    (hcP : IsCompact P) (hneP : P.Nonempty) (hKP : K ⊆ P) (u : Space d) :
    compactSupportHeight K u ≤ compactSupportHeight P u := by
  obtain ⟨q, hq, heq⟩ := compact_support_height_attained K hcK hneK u
  rw [← heq]
  exact compact_support_height_bound P hcP hneP u q (hKP hq)

theorem compact_support_height_raw_abs_bound
    (P : Set (Space d)) (hc : IsCompact P) (hne : P.Nonempty)
    (M : ℝ) (hbound : P ⊆ closedBall (0 : Space d) M) (x : Fin d → ℝ) :
    |compactSupportHeight P (WithLp.toLp 2 x)| ≤ ‖WithLp.toLp 2 x‖ * M := by
  obtain ⟨q, hq, heq⟩ := compact_support_height_attained P hc hne (WithLp.toLp 2 x)
  have hqM : ‖q‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hbound hq
  rw [← heq]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hqM (norm_nonneg _))

theorem unit_ball_support_height_test_integrable
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (P : Set (Space d)) (hc : IsCompact P) (hne : P.Nonempty)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x)) ν := by
  apply (integrable_const M).mono'
    (((continuous_compact_support_height P hc hne).comp
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).aestronglyMeasurable)
  filter_upwards [hball] with x hx
  rw [Real.norm_eq_abs]
  exact (compact_support_height_raw_abs_bound P hc hne M hbound x).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx hM)

/-- A finite measurable assignment has an integrable actual Euclidean error
under the actual unit-ball law, without assuming a cost-integrability premise. -/
theorem finite_assignment_error_integrable_of_unit_ball {n : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (w : Fin (n + 1) → Fin d → ℝ) (r : (Fin d → ℝ) → Fin (n + 1))
    (hr : Measurable r) :
    Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖) ν := by
  have hwsel : Measurable (fun x => WithLp.toLp 2 (w (r x))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
      ((measurable_of_finite w).comp hr)
  apply (integrable_const (1 + ∑ i, ‖WithLp.toLp 2 (w i)‖)).mono'
    (((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.sub hwsel).norm.aestronglyMeasurable)
  filter_upwards [hball] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (norm_sub_le _ _).trans (add_le_add hx
    (Finset.single_le_sum (fun i _ => norm_nonneg (WithLp.toLp 2 (w i))) (Finset.mem_univ (r x))))

theorem support_height_assignment_pointwise_bound {n : ℕ}
    (P : Set (Space d)) (hc : IsCompact P) (hne : P.Nonempty)
    (M : ℝ) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (x : Fin d → ℝ) :
    compactSupportHeight P (WithLp.toLp 2 x) ≤
      1 + M * ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ := by
  have hR : ∀ q ∈ P, ‖q‖ ≤ M := fun q hq => by
    simpa only [mem_closedBall, dist_zero_right] using hbound hq
  simpa only [hw (r x), mul_comm] using
    compact_support_height_lipschitz P hc hne M hR
      (WithLp.toLp 2 x) (WithLp.toLp 2 (w (r x)))

/-- The same supplied anchors and assignment give the actual support test
bound. Integrability of the test and the assignment error is proved here. -/
theorem unit_ball_support_height_assignment_test_bound {n : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (P : Set (Space d)) (hc : IsCompact P) (hne : P.Nonempty)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x)) ν ∧
      Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖) ν ∧
      (∫ x, compactSupportHeight P (WithLp.toLp 2 x) ∂ν) ≤
        1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖ ∂ν := by
  have hi := unit_ball_support_height_test_integrable ν hball P hc hne M hM hbound
  have he := finite_assignment_error_integrable_of_unit_ball ν hball w r hr
  refine ⟨hi, he, ?_⟩
  calc
    _ ≤ ∫ x, (1 + M * ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖) ∂ν :=
      integral_mono hi ((integrable_const (1 : ℝ)).add (he.const_mul M))
        (support_height_assignment_pointwise_bound P hc hne M hbound w hw r)
    _ = _ := by
      rw [integral_add (integrable_const (1 : ℝ)) (he.const_mul M), integral_const_mul]
      simp

theorem compact_cone_law_support_height_assignment_test_bound {n : ℕ}
    (μ : ProbabilityMeasure (CompactConeBall d))
    (P : Set (Space d)) (hc : IsCompact P) (hne : P.Nonempty)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x))
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
        1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) :=
  unit_ball_support_height_assignment_test_bound _ (compactBallRawLaw_ae_unit_ball μ)
    P hc hne M hM hbound w hw r hr

end SupportTest

section ActualFiniteFacetTest

variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

omit [Nontrivial (Space d)] in
theorem finite_halfspace_support_height_test_integrable
    (n : ι → Space d) (h : ι → ℝ) (P : Set (Space d)) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x))
      (finiteHalfspaceConeLaw n h) :=
  finite_cone_integrable _ _ _ _ _

/-- The actual finite-facet sum equals the support test integral under its
actual cone law. This is a discrete integral formula, with no volume derivative
or Minkowski inequality premise or conclusion. -/
theorem finite_halfspace_support_height_test_integral
    (n : ι → Space d) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (hh : ∀ i, 0 < h i) (hcQ : IsCompact (finiteHalfspaceSet n h))
    (P : Set (Space d)) (hcP : IsCompact P) (hneP : P.Nonempty) :
    (∫ x, compactSupportHeight P (WithLp.toLp 2 x) ∂finiteHalfspaceConeLaw n h) =
      (∑ i, finiteHalfspaceFacetArea n h i * compactSupportHeight P (n i)) /
        ((finrank ℝ (Space d) : ℝ) * (volume (finiteHalfspaceSet n h)).toReal) := by
  unfold finiteHalfspaceConeLaw
  rw [finite_cone_integral _ _ _ _ (finite_halfspace_facet_area_nonneg n h) hh
    (finite_halfspace_normalization_pos n h hn hh hcQ), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have heq : WithLp.toLp 2 (finiteConePoint (fun i j => n i j) h i) = (h i)⁻¹ • n i := by
    ext j
    simp [finiteConePoint, div_eq_mul_inv, mul_comm]
  rw [heq, compact_support_height_direction_nonnegative_smul P hcP hneP _
    (inv_nonneg.mpr (hh i).le)]
  field_simp [(hh i).ne']

end ActualFiniteFacetTest

section ActualLimitTest

variable {d : ℕ} [Nontrivial (Space d)]

theorem halfspace_approximation_support_height_test_integral
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ)
    (P : Set (Space d)) (hcP : IsCompact P) (hneP : P.Nonempty) :
    (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
      ∂halfspaceApproximationLaw K hc hconv hb m) =
      (∑ i : halfspaceApproximationNormals K hc hconv hb m,
        finiteHalfspaceFacetArea
          (fun u : halfspaceApproximationNormals K hc hconv hb m => (u : Space d))
          (fun u => compactSupportHeight K (u : Space d)) i *
            compactSupportHeight P (i : Space d)) /
        ((d : ℝ) * (volume (halfspaceApproximationBody K hc hconv hb m)).toReal) := by
  simpa only [halfspaceApproximationLaw, halfspaceApproximationBody, finrank_euclideanSpace_fin] using
    finite_halfspace_support_height_test_integral _ _
      (halfspace_approximation_normals_unit K hc hconv hb m)
      (halfspace_approximation_heights_pos K hc hconv hb m)
      (halfspace_approximation_body_compact K hc hconv hb m) P hcP hneP

theorem actual_body_support_height_test_integral_tendsto
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) (P : Set (Space d)) (hcP : IsCompact P) (hneP : P.Nonempty) :
    Tendsto (fun k => ∫ x, compactSupportHeight P (WithLp.toLp 2 x)
      ∂halfspaceApproximationLaw K hc hconv hb (φ k)) atTop
      (𝓝 (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)))) := by
  exact compactBallLaw_raw_integral_tendsto
    (halfspaceApproximationProbability K hc hconv hb)
    (halfspace_approximation_law_ae_unit_ball K hc hconv hb) μ φ hlim _
    ((continuous_compact_support_height P hcP hneP).comp
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)))

theorem actual_body_support_height_facet_sum_tendsto
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ)) (P : Set (Space d)) (hcP : IsCompact P) (hneP : P.Nonempty) :
    Tendsto (fun k =>
      (∑ i : halfspaceApproximationNormals K hc hconv hb (φ k),
        finiteHalfspaceFacetArea
          (fun u : halfspaceApproximationNormals K hc hconv hb (φ k) => (u : Space d))
          (fun u => compactSupportHeight K (u : Space d)) i *
            compactSupportHeight P (i : Space d)) /
        ((d : ℝ) * (volume (halfspaceApproximationBody K hc hconv hb (φ k))).toReal)) atTop
      (𝓝 (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)))) := by
  simpa only [halfspace_approximation_support_height_test_integral K hc hconv hb _ P hcP hneP] using
    actual_body_support_height_test_integral_tendsto K hc hconv hb μ φ hlim P hcP hneP

omit [Nontrivial (Space d)] in
/-- An enclosing test body contains a point because it encloses the actual
normalized K. This wrapper retains the supplied law and supplied assignment. -/
theorem actual_body_enclosing_support_height_assignment_test_bound {n : ℕ}
    (K : Set (Space d)) (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d))
    (P : Set (Space d)) (hcP : IsCompact P) (hKP : K ⊆ P)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x))
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
        1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) :=
  compact_cone_law_support_height_assignment_test_bound μ P hcP
    ⟨0, hKP (hb (by simp))⟩ M hM hbound w hw r hr

/-- Fixed original-body polar support supplies the lower test bound for an
enclosing body. The upper bound uses exactly the supplied assignment. -/
theorem actual_body_enclosing_support_height_assignment_test_bounds {n : ℕ}
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
      atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hKP : K ⊆ P)
    (M : ℝ) (hM : 0 ≤ M) (hbound : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    Integrable (fun x => compactSupportHeight P (WithLp.toLp 2 x))
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      Integrable (fun x => ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
      (1 ≤ ∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ∧
      (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
        1 + M * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := by
  obtain ⟨hi, he, hu⟩ := actual_body_enclosing_support_height_assignment_test_bound K hb μ
    P hcP hKP M hM hbound w hw r hr
  refine ⟨hi, he, ?_, hu⟩
  have hneK : K.Nonempty := ⟨0, hb (by simp)⟩
  have hneP : P.Nonempty := ⟨0, hKP (hb (by simp))⟩
  have hcarry := actual_body_compact_limit_raw_ae_polar_boundary K hc hconv hb μ φ hlim
  calc
    1 = ∫ _x : Fin d → ℝ, (1 : ℝ) ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const (1 : ℝ)) hi
      filter_upwards [hcarry] with x hx
      change compactSupportHeight K (WithLp.toLp 2 x) = 1 at hx
      rw [← hx]
      exact compact_support_height_mono K P hc hneK hcP hneP hKP (WithLp.toLp 2 x)

end ActualLimitTest
end Entry005
