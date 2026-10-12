import Entry005.PyramidMomentDefect

/-! The finite-basis compactness argument is adapted to arbitrary ambient
inner-product spaces from OpenAI/math `Brightness.lean`, theorems
`projectionBody_norm_le` and `projectionBody_isCompact`, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators RealInnerProductSpace Pointwise Topology
namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pyramidSet_mono {K L : Set E} (h : K ⊆ L) : pyramidSet K ⊆ pyramidSet L :=
  convexHull_mono (Set.union_subset_union (Set.image_mono h) (Set.Subset.refl _))

theorem pyramidSet_zero_mem {K : Set E} (h : (0 : E) ∈ K) :
    (0 : WithLp 2 (E × ℝ)) ∈ pyramidSet K := by
  apply subset_convexHull ℝ
  exact Set.mem_union_left _ ⟨0, h, by simp⟩

theorem pyramidSet_apex_mem (K : Set E) : pyramidApex ∈ pyramidSet K :=
  (subset_convexHull ℝ _) (Set.mem_union_right _ (Set.mem_singleton _))

/-- An isotropic dilation of the base also contains its canonical height-one pyramid. -/
theorem pyramidSet_subset_dilation {K L : Set E} (hzero : (0 : E) ∈ K)
    (a : ℝ) (ha : 1 ≤ a) (hLK : L ⊆ a • K) : pyramidSet L ⊆ a • pyramidSet K := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  apply convexHull_min _ ((convex_convexHull ℝ _).smul a)
  rintro p (⟨x, hx, rfl⟩ | hp)
  · obtain ⟨z, hz, rfl⟩ := hLK hx
    refine ⟨WithLp.toLp 2 (z, (0 : ℝ)), (subset_convexHull ℝ _)
      (Set.mem_union_left _ ⟨z, hz, rfl⟩), ?_⟩
    change a • WithLp.toLp 2 (z, (0 : ℝ)) = WithLp.toLp 2 (a • z, (0 : ℝ))
    rw [← WithLp.toLp_smul]
    simp
  · rcases Set.mem_singleton_iff.mp hp with rfl
    refine ⟨a⁻¹ • pyramidApex, ?_, ?_⟩
    · exact (convex_convexHull ℝ _).smul_mem_of_zero_mem (pyramidSet_zero_mem hzero)
        (pyramidSet_apex_mem K) ⟨(inv_pos.mpr ha0).le, inv_le_one_of_one_le₀ ha⟩
    · change a • (a⁻¹ • pyramidApex) = pyramidApex
      rw [smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem projectionVolumeSet_neg_normal (K : Set E) (u : E) :
    projectionVolumeSet K (-u) = projectionVolumeSet K u := by
  unfold projectionVolumeSet
  exact congrArg (fun P : Submodule ℝ E => (volume (Pᗮ.orthogonalProjectionOnto '' K)).toReal)
    (by simpa only [neg_one_smul] using
      (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0)) (x := u)))

/-- Actual projection bodies are compact by a finite orthonormal coordinate bound. -/
theorem actual_projection_body_compact_general (K : Set E) :
    IsCompact (projectionBodySet K) := by
  let b := stdOrthonormalBasis ℝ E
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨projection_body_closed K, isBounded_iff_forall_norm_le.mpr
    ⟨∑ i, projectionVolumeSet K (b i), ?_⟩⟩
  intro y hy
  calc
    ‖y‖ = ‖∑ i, inner ℝ (b i) y • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖inner ℝ (b i) y • b i‖ := norm_sum_le _ _
    _ = ∑ i, |inner ℝ (b i) y| := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, projectionVolumeSet K (b i) := by
      apply Finset.sum_le_sum
      intro i _
      apply abs_le.mpr
      constructor
      · have h := hy (-b i) (by simp)
        simpa only [inner_neg_left, projectionVolumeSet_neg_normal, neg_neg] using neg_le_neg h
      · exact hy (b i) (by simp)

theorem tendsto_pyramid_projection_ratio_of_dilation_sandwich
    (K : Set E) (P : ℕ → Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hP : ∀ m, IsCompact (P m)) (hPc : ∀ m, Convex ℝ (P m))
    (hzero : (0 : E) ∈ K) (hV : (volume K).toReal ≠ 0)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hlim : Tendsto δ atTop (𝓝 0))
    (hKP : ∀ m, K ⊆ P m) (hPK : ∀ m, P m ⊆ (1 + δ m) • K) :
    Tendsto (fun m => projectionRatio (pyramidSet (P m))) atTop
      (𝓝 (projectionRatio (pyramidSet K))) := by
  apply tendsto_projection_ratio_of_dilation_sandwich (pyramidSet K)
    (fun m => pyramidSet (P m)) (pyramidSet_compact hc hconv)
    (fun m => pyramidSet_compact (hP m) (hPc m))
    (actual_projection_body_compact_general _) _ δ hδ hlim
    (fun m => pyramidSet_mono (hKP m))
    (fun m => pyramidSet_subset_dilation hzero _ (by linarith [hδ m]) (hPK m))
  rw [pyramidSet_volume hc hconv]
  exact div_ne_zero hV (by positivity)

theorem tendsto_entryA_of_dilation_sandwich
    (K : Set E) (P : ℕ → Set E) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hP : ∀ m, IsCompact (P m)) (hPc : ∀ m, Convex ℝ (P m))
    (hzero : (0 : E) ∈ K) (hV : (volume K).toReal ≠ 0)
    (hQ : projectionRatio K ≠ 0)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hlim : Tendsto δ atTop (𝓝 0))
    (hKP : ∀ m, K ⊆ P m) (hPK : ∀ m, P m ⊆ (1 + δ m) • K) :
    Tendsto (fun m => entryA (P m)) atTop (𝓝 (entryA K)) := by
  have htP := tendsto_pyramid_projection_ratio_of_dilation_sandwich K P hc hconv
    hP hPc hzero hV δ hδ hlim hKP hPK
  have htK := tendsto_projection_ratio_of_dilation_sandwich K P hc hP
    (actual_projection_body_compact_general K) hV δ hδ hlim hKP hPK
  exact ((htP.const_mul _).div htK hQ).sub_const 1

end Entry005
