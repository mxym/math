import Entry005.AffinePyramid
import Entry005.IntrinsicLinearImageReuse
import Entry005.RadialConeVolume
import Mathlib.Analysis.Convex.Join

noncomputable section
open MeasureTheory
open scoped Pointwise
namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pyramidBaseMap : E →ₗ[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm.toLinearMap.comp
    (LinearMap.id.prod (0 : E →ₗ[ℝ] ℝ))

@[simp] theorem pyramidBaseMap_apply (x : E) :
    pyramidBaseMap x = WithLp.toLp 2 (x, (0 : ℝ)) := rfl

def pyramidApex : WithLp 2 (E × ℝ) := WithLp.toLp 2 ((0 : E), (1 : ℝ))

def pyramidReflectionLinear : WithLp 2 (E × ℝ) ≃ₗ[ℝ] WithLp 2 (E × ℝ) where
  toFun p := WithLp.toLp 2 (p.ofLp.1, -p.ofLp.2)
  invFun p := WithLp.toLp 2 (p.ofLp.1, -p.ofLp.2)
  left_inv p := by apply WithLp.ofLp_injective; ext <;> simp
  right_inv p := by apply WithLp.ofLp_injective; ext <;> simp
  map_add' p q := by
    change WithLp.toLp 2 (p.ofLp.1 + q.ofLp.1, -(p.ofLp.2 + q.ofLp.2)) = _
    rw [← WithLp.toLp_add]
    simp [add_comm]
  map_smul' a p := by
    change WithLp.toLp 2 (a • p.ofLp.1, -(a * p.ofLp.2)) = _
    rw [← WithLp.toLp_smul]
    simp

def pyramidReflection : WithLp 2 (E × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (E × ℝ) where
  toLinearEquiv := pyramidReflectionLinear
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    simp [pyramidReflectionLinear]

def pyramidFlip : WithLp 2 (E × ℝ) ≃ᵃ[ℝ] WithLp 2 (E × ℝ) :=
  AffineEquiv.ofLinearEquiv pyramidReflection.toLinearEquiv 0 pyramidApex

@[simp] theorem pyramidFlip_apply (x : E) (t : ℝ) :
    pyramidFlip (WithLp.toLp 2 (x, t)) = WithLp.toLp 2 (x, 1 - t) := by
  simp only [pyramidFlip, AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub,
    sub_zero, vadd_eq_add]
  change WithLp.toLp 2 (x, -t) + WithLp.toLp 2 (0, 1) = _
  rw [← WithLp.toLp_add]
  simp [sub_eq_add_neg, add_comm]

theorem pyramidSet_eq_flip_radial {K : Set E} (hK : Convex ℝ K) :
    pyramidSet K =
      pyramidFlip '' ((WithLp.toLp 2) '' radialCone K 1) ∪ {pyramidApex} := by
  by_cases hne : K.Nonempty
  · have hb : Convex ℝ (pyramidBaseMap '' K) := hK.linear_image pyramidBaseMap
    have hs : pyramidSet K = convexJoin ℝ {pyramidApex} (pyramidBaseMap '' K) := by
      unfold pyramidSet
      change convexHull ℝ (pyramidBaseMap '' K ∪ {pyramidApex}) = _
      rw [hb.convexHull_union (convex_singleton _) (hne.image _) (Set.singleton_nonempty _),
        convexJoin_comm]
    rw [hs]
    ext p
    constructor
    · intro hp
      rcases mem_convexJoin.mp hp with ⟨a, ha, b, hb, hseg⟩
      rcases Set.mem_singleton_iff.mp ha with rfl
      rcases hb with ⟨x, hx, rfl⟩
      rw [segment_eq_image] at hseg
      obtain ⟨t, ht, rfl⟩ := hseg
      apply Set.mem_union_left
      refine ⟨WithLp.toLp 2 (t • x, t), ⟨(t • x, t), ⟨t, ht, x, hx, by simp⟩, rfl⟩, ?_⟩
      rw [pyramidFlip_apply, pyramidBaseMap_apply]
      simp only [pyramidApex, ← WithLp.toLp_smul, ← WithLp.toLp_add]
      simp
    · rintro (⟨q, ⟨z, ⟨t, ht, x, hx, rfl⟩, rfl⟩, rfl⟩ | hp)
      · apply mem_convexJoin.mpr
        refine ⟨pyramidApex, rfl, pyramidBaseMap x, ⟨x, hx, rfl⟩, ?_⟩
        rw [segment_eq_image]
        refine ⟨t, ht, ?_⟩
        rw [pyramidFlip_apply, pyramidBaseMap_apply]
        simp only [pyramidApex, ← WithLp.toLp_smul, ← WithLp.toLp_add]
        simp
      · rcases Set.mem_singleton_iff.mp hp with rfl
        exact subset_convexJoin_left (hne.image _) (Set.mem_singleton _)
  · have hzero : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hzero, pyramidSet, radialCone, pyramidApex, convexHull_singleton]

/-- Literal parametrization, retaining the apex even for an empty base. -/
theorem mem_pyramidSet_iff {K : Set E} (hK : Convex ℝ K) (p : WithLp 2 (E × ℝ)) :
    p ∈ pyramidSet K ↔ p = pyramidApex ∨
      ∃ r ∈ Set.Icc (0 : ℝ) 1, ∃ z ∈ K, p = WithLp.toLp 2 (r • z, 1 - r) := by
  rw [pyramidSet_eq_flip_radial hK]
  constructor
  · rintro (⟨q, ⟨v, ⟨r, hr, z, hz, rfl⟩, rfl⟩, rfl⟩ | hp)
    · exact Or.inr ⟨r, hr, z, hz, by rw [pyramidFlip_apply]; simp⟩
    · exact Or.inl (Set.mem_singleton_iff.mp hp)
  · rintro (rfl | ⟨r, hr, z, hz, rfl⟩)
    · exact Set.mem_union_right _ (Set.mem_singleton _)
    · apply Set.mem_union_left
      refine ⟨WithLp.toLp 2 (r • z, r), ⟨(r • z, r), ⟨r, hr, z, hz, by simp⟩, rfl⟩, ?_⟩
      rw [pyramidFlip_apply]

section Volume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pyramidSet_compact {K : Set E} (hc : IsCompact K) (hconv : Convex ℝ K) :
    IsCompact (pyramidSet K) := by
  rw [pyramidSet_eq_flip_radial hconv]
  have hf : Continuous (pyramidFlip : WithLp 2 (E × ℝ) → WithLp 2 (E × ℝ)) := by
    have he : (pyramidFlip : WithLp 2 (E × ℝ) → WithLp 2 (E × ℝ)) =
        (fun p => pyramidReflection p + pyramidApex) := by
      funext p
      simp [pyramidFlip, AffineEquiv.ofLinearEquiv_apply, vadd_eq_add]
    rw [he]
    exact pyramidReflection.continuous.add continuous_const
  exact (((radial_cone_compact hc 1).image (WithLp.prod_continuous_toLp 2 E ℝ)).image
    hf).union isCompact_singleton

theorem pyramidFlip_volume (S : Set (WithLp 2 (E × ℝ))) :
    volume (pyramidFlip '' S) = volume S := by
  have hi : pyramidFlip '' S =
      (fun x : WithLp 2 (E × ℝ) => pyramidApex + x) '' (pyramidReflection '' S) := by
    rw [Set.image_image]
    congr 1
    funext p
    simp [pyramidFlip, AffineEquiv.ofLinearEquiv_apply, vadd_eq_add, add_comm]
  rw [hi, IntrinsicLinearImageReuse.translation_volume_image,
    IntrinsicLinearImageReuse.isometry_volume_image]

/-- Actual volume of the canonical compact convex pyramid, from genuine Fubini slices.
The empty base is included; no pyramid-volume identity is an input. -/
theorem pyramidSet_volume {K : Set E} (hc : IsCompact K) (hconv : Convex ℝ K) :
    (volume (pyramidSet K)).toReal =
      (volume K).toReal / (Module.finrank ℝ E + 1 : ℝ) := by
  rw [pyramidSet_eq_flip_radial hconv]
  have hz : volume ({pyramidApex} : Set (WithLp 2 (E × ℝ))) = 0 := by simp
  have hu : volume (pyramidFlip '' (WithLp.toLp 2 '' radialCone K 1) ∪ {pyramidApex}) =
      volume (pyramidFlip '' (WithLp.toLp 2 '' radialCone K 1)) := by
    apply le_antisymm
    · simpa [hz] using measure_union_le (μ := volume) (pyramidFlip '' (WithLp.toLp 2 '' radialCone K 1))
        ({pyramidApex} : Set (WithLp 2 (E × ℝ)))
    · exact measure_mono Set.subset_union_left
  rw [hu, pyramidFlip_volume,
    radial_cone_lp_volume hc (by norm_num)]
  ring

end Volume
end Entry005
