import Entry005.HalfspaceApproximation

noncomputable section
open Metric MeasureTheory Module Function Filter
open scoped BigOperators RealInnerProductSpace Pointwise Topology

namespace Entry005

section ScalarVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem real_volume_nonnegative_smul (K : Set E) (a : ℝ) (ha : 0 ≤ a) :
    (volume (a • K)).toReal = a ^ finrank ℝ E * (volume K).toReal := by
  rw [Measure.addHaar_smul_of_nonneg volume ha K, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha _)]

theorem compact_real_volume_mono (K L : Set E) (hL : IsCompact L) (hKL : K ⊆ L) :
    (volume K).toReal ≤ (volume L).toReal :=
  ENNReal.toReal_mono hL.measure_ne_top (measure_mono hKL)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthogonal_projection_smul_image (K : Set E) (u : E) (a : ℝ) :
    (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' (a • K) =
      a • ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' K) := by
  ext y
  constructor
  · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    rw [map_smul]
    exact Set.smul_mem_smul_set (Set.mem_image_of_mem _ hq)
  · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨a • q, Set.smul_mem_smul_set hq, map_smul _ _ _⟩

theorem projection_volume_nonnegative_smul (K : Set E) (u : E) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    projectionVolumeSet (a • K) u = a ^ (finrank ℝ E - 1) * projectionVolumeSet K u := by
  unfold projectionVolumeSet
  rw [orthogonal_projection_smul_image, real_volume_nonnegative_smul _ a ha]
  have hdim : finrank ℝ (ℝ ∙ u)ᗮ = finrank ℝ E - 1 := by
    have hd := unit_normal_hyperplane_finrank_add_one u hu
    omega
  rw [hdim]

theorem projection_volume_mono (K L : Set E) (hL : IsCompact L) (hKL : K ⊆ L) (u : E) :
    projectionVolumeSet K u ≤ projectionVolumeSet L u := by
  apply compact_real_volume_mono _ _ (hL.image (ℝ ∙ u)ᗮ.orthogonalProjectionOnto.continuous)
  exact Set.image_mono hKL

theorem projection_body_mono (K L : Set E) (hL : IsCompact L) (hKL : K ⊆ L) :
    projectionBodySet K ⊆ projectionBodySet L := by
  intro x hx u hu
  exact (hx u hu).trans (projection_volume_mono K L hL hKL u)

theorem projection_body_positive_smul (K : Set E) (a : ℝ) (ha : 0 < a) :
    projectionBodySet (a • K) = (a ^ (finrank ℝ E - 1)) • projectionBodySet K := by
  let c := a ^ (finrank ℝ E - 1)
  have hc : 0 < c := pow_pos ha _
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • x, ?_, ?_⟩
    · intro u hu
      have hb := hx u hu
      rw [projection_volume_nonnegative_smul K u hu a ha.le] at hb
      rw [inner_smul_right]
      exact (inv_mul_le_iff₀ hc).mpr hb
    · change c • (c⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩ u hu
    rw [inner_smul_right, projection_volume_nonnegative_smul K u hu a ha.le]
    exact mul_le_mul_of_nonneg_left (hy u hu) hc.le

theorem projection_body_closed (K : Set E) : IsClosed (projectionBodySet K) := by
  have heq : projectionBodySet K = ⋂ u : E, ⋂ (_ : ‖u‖ = 1),
      {x : E | inner ℝ u x ≤ projectionVolumeSet K u} := by
    ext x
    simp [projectionBodySet]
  rw [heq]
  exact isClosed_iInter (fun u => isClosed_iInter (fun _ => isClosed_le
    (show Continuous (fun x : E => inner ℝ u x) from continuous_const.inner continuous_id)
    continuous_const))

theorem projection_body_convex (K : Set E) : Convex ℝ (projectionBodySet K) := by
  intro x hx y hy a b ha hb hab u hu
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hax := mul_le_mul_of_nonneg_left (hx u hu) ha
  have hby := mul_le_mul_of_nonneg_left (hy u hu) hb
  have habc : a * projectionVolumeSet K u + b * projectionVolumeSet K u = projectionVolumeSet K u := by
    rw [← add_mul, hab, one_mul]
  linarith

theorem projection_body_zero_mem (K : Set E) : (0 : E) ∈ projectionBodySet K := by
  intro u _
  rw [inner_zero_right]
  exact ENNReal.toReal_nonneg

theorem compact_body_volume_pos_of_unit_ball (K : Set E) (hc : IsCompact K)
    (hb : closedBall (0 : E) 1 ⊆ K) : 0 < (volume K).toReal := by
  have hne : (interior K).Nonempty := by
    refine ⟨0, (interior_mono (ball_subset_closedBall.trans hb)) ?_⟩
    rw [isOpen_ball.interior_eq]
    simp
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hne).ne' hc.measure_ne_top

theorem compact_body_normalization_pos_of_unit_ball [Nontrivial E] (K : Set E) (hc : IsCompact K)
    (hb : closedBall (0 : E) 1 ⊆ K) :
    0 < (finrank ℝ E : ℝ) * (volume K).toReal := by
  exact mul_pos (by exact_mod_cast (finrank_pos : 0 < finrank ℝ E))
    (compact_body_volume_pos_of_unit_ball K hc hb)

end ScalarVolume

section ActualProjectedBalls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonal_projection_closed_ball (u : E) (R : ℝ) :
    (ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' closedBall (0 : E) R =
      closedBall (0 : (ℝ ∙ u)ᗮ) R := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [mem_closedBall, dist_zero_right] at hx ⊢
    exact ((ℝ ∙ u)ᗮ.norm_orthogonalProjectionOnto_apply_le x).trans hx
  · intro hy
    refine ⟨(y : E), ?_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
    simpa only [mem_closedBall, dist_zero_right, Submodule.norm_coe] using hy

end ActualProjectedBalls

section NormalizedProjectionBody

variable {d : ℕ} [Nontrivial (Space d)]

def unitProjectionBallVolume (d : ℕ) : ℝ :=
  (volume (closedBall (0 : Space (d - 1)) 1)).toReal

omit [Nontrivial (Space d)] in
theorem unit_projection_ball_volume_pos : 0 < unitProjectionBallVolume d := by
  have hp : 0 < volume (ball (0 : Space (d - 1)) 1) := isOpen_ball.measure_pos volume ⟨0, by simp⟩
  have hpc : 0 < volume (closedBall (0 : Space (d - 1)) 1) := hp.trans_le (measure_mono ball_subset_closedBall)
  exact ENNReal.toReal_pos hpc.ne' (isCompact_closedBall (0 : Space (d - 1)) (1 : ℝ)).measure_ne_top

theorem projection_volume_closed_ball (u : Space d) (hu : ‖u‖ = 1) (R : ℝ) (hR : 0 ≤ R) :
    projectionVolumeSet (closedBall (0 : Space d) R) u =
      R ^ (d - 1) * unitProjectionBallVolume d := by
  unfold projectionVolumeSet
  rw [orthogonal_projection_closed_ball]
  have hv := Measure.addHaar_closedBall_mul volume (0 : (ℝ ∙ u)ᗮ) hR (by norm_num : (0 : ℝ) ≤ 1)
  simp only [mul_one] at hv
  rw [hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR _)]
  have hdim : finrank ℝ (ℝ ∙ u)ᗮ = d - 1 := by
    have hd := unit_normal_hyperplane_finrank_add_one u hu
    rw [finrank_euclideanSpace_fin] at hd
    omega
  rw [hdim, unit_hyperplane_ball_volume u hu]
  rfl

theorem normalized_body_brightness_lower (K : Set (Space d)) (hc : IsCompact K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (u : Space d) (hu : ‖u‖ = 1) :
    unitProjectionBallVolume d ≤ projectionVolumeSet K u := by
  have hm := projection_volume_mono (closedBall (0 : Space d) 1) K hc hb u
  rw [projection_volume_closed_ball u hu 1 (by norm_num), one_pow, one_mul] at hm
  exact hm

theorem bounded_body_brightness_upper (K : Set (Space d)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : K ⊆ closedBall (0 : Space d) R) (u : Space d) (hu : ‖u‖ = 1) :
    projectionVolumeSet K u ≤ R ^ (d - 1) * unitProjectionBallVolume d := by
  have hm := projection_volume_mono K (closedBall (0 : Space d) R) (isCompact_closedBall _ _) hbound u
  rw [projection_volume_closed_ball u hu R hR] at hm
  exact hm

theorem normalized_projection_body_contains_ball (K : Set (Space d)) (hc : IsCompact K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    closedBall (0 : Space d) (unitProjectionBallVolume d) ⊆ projectionBodySet K := by
  intro x hx u hu
  have hxn : ‖x‖ ≤ unitProjectionBallVolume d := by simpa only [mem_closedBall, dist_zero_right] using hx
  calc
    inner ℝ u x ≤ ‖u‖ * ‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [hu, one_mul]
    _ ≤ unitProjectionBallVolume d := hxn
    _ ≤ projectionVolumeSet K u := normalized_body_brightness_lower K hc hb u hu

theorem bounded_projection_body_subset_ball (K : Set (Space d)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : K ⊆ closedBall (0 : Space d) R) :
    projectionBodySet K ⊆ closedBall (0 : Space d) (R ^ (d - 1) * unitProjectionBallVolume d) := by
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]
    exact mul_nonneg (pow_nonneg hR _) unit_projection_ball_volume_pos.le
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let u : Space d := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnx), inv_mul_cancel₀ hnx.ne']
  have hux : inner ℝ u x = ‖x‖ := by
    dsimp [u]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hnx.ne', one_mul]
  have hm := (hx u hu).trans (bounded_body_brightness_upper K R hR hbound u hu)
  simpa only [hux] using hm

theorem bounded_projection_body_compact (K : Set (Space d)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : K ⊆ closedBall (0 : Space d) R) : IsCompact (projectionBodySet K) :=
  (isCompact_closedBall _ _).of_isClosed_subset (projection_body_closed K)
    (bounded_projection_body_subset_ball K R hR hbound)

theorem normalized_projection_body_volume_pos (K : Set (Space d)) (hc : IsCompact K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (R : ℝ) (hR : 0 ≤ R)
    (hbound : K ⊆ closedBall (0 : Space d) R) :
    0 < (volume (projectionBodySet K)).toReal := by
  have hball := normalized_projection_body_contains_ball K hc hb
  have hne : (interior (projectionBodySet K)).Nonempty := by
    refine ⟨0, (interior_mono (ball_subset_closedBall.trans hball)) ?_⟩
    rw [isOpen_ball.interior_eq]
    simpa only [mem_ball, dist_self] using (unit_projection_ball_volume_pos (d := d))
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hne).ne'
    (bounded_projection_body_compact K R hR hbound).measure_ne_top

theorem normalized_projection_ratio_pos (K : Set (Space d)) (hc : IsCompact K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (R : ℝ) (hR : 0 ≤ R)
    (hbound : K ⊆ closedBall (0 : Space d) R) : 0 < projectionRatio K := by
  exact div_pos (normalized_projection_body_volume_pos K hc hb R hR hbound)
    (pow_pos (compact_body_volume_pos_of_unit_ball K hc hb) _)

end NormalizedProjectionBody

section DilationSqueezes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem compact_real_volume_dilation_sandwich (K P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (a : ℝ) (ha : 0 ≤ a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) :
    (volume K).toReal ≤ (volume P).toReal ∧
      (volume P).toReal ≤ a ^ finrank ℝ E * (volume K).toReal := by
  refine ⟨compact_real_volume_mono K P hP hKP, ?_⟩
  have hm := compact_real_volume_mono P (a • K) (hK.image (continuous_const.smul continuous_id)) hPK
  rw [real_volume_nonnegative_smul K a ha] at hm
  exact hm

theorem compact_projection_volume_dilation_sandwich (K P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (a : ℝ) (ha : 0 ≤ a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) (u : E) (hu : ‖u‖ = 1) :
    projectionVolumeSet K u ≤ projectionVolumeSet P u ∧
      projectionVolumeSet P u ≤ a ^ (finrank ℝ E - 1) * projectionVolumeSet K u := by
  refine ⟨projection_volume_mono K P hP hKP u, ?_⟩
  have hm := projection_volume_mono P (a • K) (hK.image (continuous_const.smul continuous_id)) hPK u
  rw [projection_volume_nonnegative_smul K u hu a ha] at hm
  exact hm

theorem compact_projection_body_dilation_sandwich (K P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (a : ℝ) (ha : 0 < a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) :
    projectionBodySet K ⊆ projectionBodySet P ∧
      projectionBodySet P ⊆ (a ^ (finrank ℝ E - 1)) • projectionBodySet K := by
  refine ⟨projection_body_mono K P hP hKP, ?_⟩
  have hm := projection_body_mono P (a • K) (hK.image (continuous_const.smul continuous_id)) hPK
  rw [projection_body_positive_smul K a ha] at hm
  exact hm

theorem compact_projection_body_of_dilation_sandwich (K P : Set E)
    (hK : IsCompact K) (hP : IsCompact P) (hBK : IsCompact (projectionBodySet K))
    (a : ℝ) (ha : 0 < a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) :
    IsCompact (projectionBodySet P) := by
  have hs := compact_projection_body_dilation_sandwich K P hK hP a ha hKP hPK
  exact (hBK.image (continuous_const.smul continuous_id)).of_isClosed_subset
    (projection_body_closed P) hs.2

theorem compact_projection_body_volume_dilation_sandwich (K P : Set E)
    (hK : IsCompact K) (hP : IsCompact P) (hBK : IsCompact (projectionBodySet K))
    (a : ℝ) (ha : 0 < a) (hKP : K ⊆ P) (hPK : P ⊆ a • K) :
    (volume (projectionBodySet K)).toReal ≤ (volume (projectionBodySet P)).toReal ∧
      (volume (projectionBodySet P)).toReal ≤
        (a ^ (finrank ℝ E - 1)) ^ finrank ℝ E * (volume (projectionBodySet K)).toReal := by
  have hs := compact_projection_body_dilation_sandwich K P hK hP a ha hKP hPK
  exact compact_real_volume_dilation_sandwich _ _ hBK
    (compact_projection_body_of_dilation_sandwich K P hK hP hBK a ha hKP hPK)
    _ (pow_nonneg ha.le _) hs.1 hs.2

theorem tendsto_real_volume_of_dilation_sandwich (K : Set E) (P : ℕ → Set E)
    (hK : IsCompact K) (hP : ∀ n, IsCompact (P n)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hlim : Tendsto δ atTop (𝓝 0)) (hKP : ∀ n, K ⊆ P n) (hPK : ∀ n, P n ⊆ (1 + δ n) • K) :
    Tendsto (fun n => (volume (P n)).toReal) atTop (𝓝 (volume K).toReal) := by
  have hu : Tendsto (fun n => (1 + δ n) ^ finrank ℝ E * (volume K).toReal)
      atTop (𝓝 (volume K).toReal) := by
    convert ((tendsto_const_nhds.add hlim).pow (finrank ℝ E)).mul_const (volume K).toReal using 1
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (compact_real_volume_dilation_sandwich K (P n) hK (hP n) _ (by linarith [hδ n])
      (hKP n) (hPK n)).1)
    (fun n => (compact_real_volume_dilation_sandwich K (P n) hK (hP n) _ (by linarith [hδ n])
      (hKP n) (hPK n)).2)

theorem tendsto_projection_volume_of_dilation_sandwich (K : Set E) (P : ℕ → Set E)
    (hK : IsCompact K) (hP : ∀ n, IsCompact (P n)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hlim : Tendsto δ atTop (𝓝 0)) (hKP : ∀ n, K ⊆ P n) (hPK : ∀ n, P n ⊆ (1 + δ n) • K)
    (u : E) (hu : ‖u‖ = 1) :
    Tendsto (fun n => projectionVolumeSet (P n) u) atTop (𝓝 (projectionVolumeSet K u)) := by
  have hupper : Tendsto (fun n => (1 + δ n) ^ (finrank ℝ E - 1) * projectionVolumeSet K u)
      atTop (𝓝 (projectionVolumeSet K u)) := by
    convert ((tendsto_const_nhds.add hlim).pow (finrank ℝ E - 1)).mul_const (projectionVolumeSet K u)
      using 1
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => (compact_projection_volume_dilation_sandwich K (P n) hK (hP n) _
      (by linarith [hδ n]) (hKP n) (hPK n) u hu).1)
    (fun n => (compact_projection_volume_dilation_sandwich K (P n) hK (hP n) _
      (by linarith [hδ n]) (hKP n) (hPK n) u hu).2)

theorem tendsto_projection_body_volume_of_dilation_sandwich (K : Set E) (P : ℕ → Set E)
    (hK : IsCompact K) (hP : ∀ n, IsCompact (P n)) (hBK : IsCompact (projectionBodySet K))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hKP : ∀ n, K ⊆ P n) (hPK : ∀ n, P n ⊆ (1 + δ n) • K) :
    Tendsto (fun n => (volume (projectionBodySet (P n))).toReal)
      atTop (𝓝 (volume (projectionBodySet K)).toReal) := by
  have hupper : Tendsto (fun n => ((1 + δ n) ^ (finrank ℝ E - 1)) ^ finrank ℝ E *
      (volume (projectionBodySet K)).toReal) atTop (𝓝 (volume (projectionBodySet K)).toReal) := by
    convert (((tendsto_const_nhds.add hlim).pow (finrank ℝ E - 1)).pow (finrank ℝ E)).mul_const
      (volume (projectionBodySet K)).toReal using 1
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => (compact_projection_body_volume_dilation_sandwich K (P n) hK (hP n) hBK _
      (by linarith [hδ n]) (hKP n) (hPK n)).1)
    (fun n => (compact_projection_body_volume_dilation_sandwich K (P n) hK (hP n) hBK _
      (by linarith [hδ n]) (hKP n) (hPK n)).2)

theorem tendsto_projection_ratio_of_dilation_sandwich (K : Set E) (P : ℕ → Set E)
    (hK : IsCompact K) (hP : ∀ n, IsCompact (P n)) (hBK : IsCompact (projectionBodySet K))
    (hV : (volume K).toReal ≠ 0) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hlim : Tendsto δ atTop (𝓝 0)) (hKP : ∀ n, K ⊆ P n) (hPK : ∀ n, P n ⊆ (1 + δ n) • K) :
    Tendsto (fun n => projectionRatio (P n)) atTop (𝓝 (projectionRatio K)) := by
  exact (tendsto_projection_body_volume_of_dilation_sandwich K P hK hP hBK δ hδ hlim hKP hPK).div
    ((tendsto_real_volume_of_dilation_sandwich K P hK hP δ hδ hlim hKP hPK).pow (finrank ℝ E - 1))
    (pow_ne_zero _ hV)

theorem tendsto_brightness_normalization_of_dilation_sandwich (K : Set E) (P : ℕ → Set E)
    (hK : IsCompact K) (hP : ∀ n, IsCompact (P n))
    (hM : (finrank ℝ E : ℝ) * (volume K).toReal ≠ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hKP : ∀ n, K ⊆ P n) (hPK : ∀ n, P n ⊆ (1 + δ n) • K) (u : E) (hu : ‖u‖ = 1) :
    Tendsto (fun n => projectionVolumeSet (P n) u /
      ((finrank ℝ E : ℝ) * (volume (P n)).toReal)) atTop
      (𝓝 (projectionVolumeSet K u / ((finrank ℝ E : ℝ) * (volume K).toReal))) := by
  exact (tendsto_projection_volume_of_dilation_sandwich K P hK hP δ hδ hlim hKP hPK u hu).div
    ((tendsto_real_volume_of_dilation_sandwich K P hK hP δ hδ hlim hKP hPK).const_mul _) hM

end DilationSqueezes
end Entry005
