import Entry005.HalfspaceApproximationSequence
import Mathlib.Analysis.Convex.Join

noncomputable section
open Metric MeasureTheory Module Filter Set
open scoped Pointwise Topology RealInnerProductSpace

namespace Entry005

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pyramidBaseLift : E →ₗ[ℝ] WithLp 2 (E × ℝ) where
  toFun x := WithLp.toLp 2 (x, (0 : ℝ))
  map_add' x y := by simp [← WithLp.toLp_add]
  map_smul' a x := by simp [← WithLp.toLp_smul]

theorem pyramid_set_convex (K : Set E) : Convex ℝ (pyramidSet K) :=
  convex_convexHull ℝ _

theorem pyramid_set_mono {K P : Set E} (hKP : K ⊆ P) : pyramidSet K ⊆ pyramidSet P :=
  convexHull_mono (union_subset_union (image_mono hKP) Subset.rfl)

theorem pyramid_base_mem {K : Set E} {x : E} (hx : x ∈ K) :
    WithLp.toLp 2 (x, (0 : ℝ)) ∈ pyramidSet K :=
  subset_convexHull ℝ _ (Or.inl (mem_image_of_mem _ hx))

theorem pyramid_apex_mem (K : Set E) :
    WithLp.toLp 2 ((0 : E), (1 : ℝ)) ∈ pyramidSet K :=
  subset_convexHull ℝ _ (Or.inr (mem_singleton _))

theorem pyramid_zero_mem {K : Set E} (h0 : (0 : E) ∈ K) :
    (0 : WithLp 2 (E × ℝ)) ∈ pyramidSet K := by
  exact pyramid_base_mem h0

theorem pyramid_set_eq_parametric_image (K : Set E) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    pyramidSet K = (fun p : ℝ × E =>
      (1 - p.1) • WithLp.toLp 2 (p.2, (0 : ℝ)) +
        p.1 • WithLp.toLp 2 ((0 : E), (1 : ℝ))) '' (Icc (0 : ℝ) 1 ×ˢ K) := by
  have hc : Convex ℝ ((pyramidBaseLift : E →ₗ[ℝ] WithLp 2 (E × ℝ)) '' K) :=
    hconv.linear_image pyramidBaseLift
  have hn : ((pyramidBaseLift : E →ₗ[ℝ] WithLp 2 (E × ℝ)) '' K).Nonempty :=
    hne.image pyramidBaseLift
  change convexHull ℝ (pyramidBaseLift '' K ∪ {WithLp.toLp 2 ((0 : E), (1 : ℝ))}) = _
  rw [hc.convexHull_union (convex_singleton _) hn (singleton_nonempty _)]
  ext y
  constructor
  · intro hy
    obtain ⟨b, ⟨x, hx, rfl⟩, a, ha, hy⟩ := mem_convexJoin.mp hy
    rw [mem_singleton_iff] at ha
    subst a
    rw [segment_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    apply mem_convexJoin.mpr
    refine ⟨pyramidBaseLift x, mem_image_of_mem _ hx, _, mem_singleton _, ?_⟩
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩

theorem pyramid_set_compact (K : Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) : IsCompact (pyramidSet K) := by
  rw [pyramid_set_eq_parametric_image K hconv hne]
  exact (isCompact_Icc.prod hc).image (by fun_prop)

theorem pyramid_set_subset_dilation {K P : Set E} (h0 : (0 : E) ∈ K)
    (a : ℝ) (ha : 1 ≤ a) (hPK : P ⊆ a • K) :
    pyramidSet P ⊆ a • pyramidSet K := by
  have hap : 0 < a := zero_lt_one.trans_le ha
  apply convexHull_min _ ((pyramid_set_convex K).smul a)
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hPK hx
    refine ⟨WithLp.toLp 2 (z, (0 : ℝ)), pyramid_base_mem hz, ?_⟩
    simp [← WithLp.toLp_smul]
  · rw [mem_singleton_iff] at hy
    subst y
    refine ⟨a⁻¹ • WithLp.toLp 2 ((0 : E), (1 : ℝ)), ?_, ?_⟩
    · have hi : 0 ≤ a⁻¹ := inv_nonneg.mpr hap.le
      have hi1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
      have hs := (pyramid_set_convex K) (pyramid_zero_mem h0)
        (pyramid_apex_mem K) (sub_nonneg.mpr hi1) hi (by ring : 1 - a⁻¹ + a⁻¹ = 1)
      simpa using hs
    · change a • (a⁻¹ • WithLp.toLp 2 ((0 : E), (1 : ℝ))) = _
      rw [smul_smul, mul_inv_cancel₀ hap.ne', one_smul]

theorem pyramid_set_dilation_sandwich {K P : Set E} (h0 : (0 : E) ∈ K)
    (a : ℝ) (ha : 1 ≤ a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) :
    pyramidSet K ⊆ pyramidSet P ∧ pyramidSet P ⊆ a • pyramidSet K :=
  ⟨pyramid_set_mono hKP, pyramid_set_subset_dilation h0 a ha hPK⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Testing the finitely many positive and negative orthonormal basis directions
gives an actual norm bound on the unit-direction projection halfspaces. -/
theorem finite_dimensional_projection_body_compact (K : Set E) :
    IsCompact (projectionBodySet K) := by
  let b := stdOrthonormalBasis ℝ E
  let C := ∑ i, max (projectionVolumeSet K (b i)) (projectionVolumeSet K (-b i))
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨projection_body_closed K, isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩⟩
  intro y hy
  calc
    ‖y‖ = ‖∑ i, inner ℝ (b i) y • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖inner ℝ (b i) y • b i‖ := norm_sum_le _ _
    _ = ∑ i, |inner ℝ (b i) y| := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      apply abs_le.mpr
      constructor
      · have hn := hy (-b i) (by simp)
        rw [inner_neg_left] at hn
        linarith [le_max_right (projectionVolumeSet K (b i)) (projectionVolumeSet K (-b i))]
      · exact (hy (b i) (b.norm_eq_one i)).trans (le_max_left _ _)

end Geometry

section ActualSequence

variable {d : ℕ}

theorem halfspace_approximation_pyramid_compact (K : Set (Space d)) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    IsCompact (pyramidSet (halfspaceApproximationBody K hc hconv hb m)) := by
  apply pyramid_set_compact _ (halfspace_approximation_body_compact K hc hconv hb m)
  · intro x hx y hy a b ha hb' hab i
    simp only [inner_add_right, inner_smul_right]
    have hax := mul_le_mul_of_nonneg_left (hx i) ha
    have hby := mul_le_mul_of_nonneg_left (hy i) hb'
    have heq : a * compactSupportHeight K (i : Space d) +
        b * compactSupportHeight K (i : Space d) = compactSupportHeight K (i : Space d) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · exact ⟨0, subset_halfspace_approximation_body K hc hconv hb m (hb (by simp))⟩

theorem halfspace_approximation_pyramid_dilation_sandwich (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    pyramidSet K ⊆ pyramidSet (halfspaceApproximationBody K hc hconv hb m) ∧
      pyramidSet (halfspaceApproximationBody K hc hconv hb m) ⊆
        (1 + halfspaceApproximationTolerance m) • pyramidSet K := by
  apply pyramid_set_dilation_sandwich (hb (by simp)) _
    (by linarith [halfspace_approximation_tolerance_pos m])
    (subset_halfspace_approximation_body K hc hconv hb m)
    (halfspace_approximation_body_subset_dilation K hc hconv hb m)

theorem halfspace_approximation_pyramid_volume_tendsto (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    Tendsto (fun m => (volume (pyramidSet (halfspaceApproximationBody K hc hconv hb m))).toReal)
      atTop (𝓝 (volume (pyramidSet K)).toReal) := by
  apply tendsto_real_volume_of_dilation_sandwich _ _
    (pyramid_set_compact K hc hconv ⟨0, hb (by simp)⟩)
    (halfspace_approximation_pyramid_compact K hc hconv hb) halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
  · exact fun m => (halfspace_approximation_pyramid_dilation_sandwich K hc hconv hb m).1
  · exact fun m => (halfspace_approximation_pyramid_dilation_sandwich K hc hconv hb m).2

theorem halfspace_approximation_pyramid_projection_body_volume_tendsto (K : Set (Space d))
    (hc : IsCompact K) (hconv : Convex ℝ K) (hb : closedBall (0 : Space d) 1 ⊆ K) :
    Tendsto (fun m => (volume (projectionBodySet
      (pyramidSet (halfspaceApproximationBody K hc hconv hb m)))).toReal)
      atTop (𝓝 (volume (projectionBodySet (pyramidSet K))).toReal) := by
  apply tendsto_projection_body_volume_of_dilation_sandwich _ _
    (pyramid_set_compact K hc hconv ⟨0, hb (by simp)⟩)
    (halfspace_approximation_pyramid_compact K hc hconv hb)
    (finite_dimensional_projection_body_compact (pyramidSet K)) halfspaceApproximationTolerance
    (fun m => (halfspace_approximation_tolerance_pos m).le) halfspace_approximation_tolerance_tendsto
  · exact fun m => (halfspace_approximation_pyramid_dilation_sandwich K hc hconv hb m).1
  · exact fun m => (halfspace_approximation_pyramid_dilation_sandwich K hc hconv hb m).2

end ActualSequence
end Entry005
