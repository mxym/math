import Entry005.FiniteHalfspaceConeLaw

noncomputable section
open Metric MeasureTheory Module Function
open scoped BigOperators RealInnerProductSpace Pointwise

namespace Entry005

section CompactSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def compactSupportHeight (K : Set E) (u : E) : ℝ :=
  sSup ((fun x : E => inner ℝ u x) '' K)

theorem compact_support_height_attained (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (u : E) : ∃ q ∈ K, inner ℝ u q = compactSupportHeight K u := by
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn hne
    (show Continuous (fun x : E => inner ℝ u x) from continuous_const.inner continuous_id).continuousOn
  refine ⟨q, hq, ?_⟩
  have hg : IsGreatest ((fun x : E => inner ℝ u x) '' K) (inner ℝ u q) := by
    refine ⟨Set.mem_image_of_mem _ hq, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact hmax hx
  exact hg.csSup_eq.symm

theorem compact_support_height_bound (K : Set E) (hc : IsCompact K) (_hne : K.Nonempty)
    (u x : E) (hx : x ∈ K) : inner ℝ u x ≤ compactSupportHeight K u := by
  exact le_csSup (hc.image (show Continuous (fun x : E => inner ℝ u x) from
    continuous_const.inner continuous_id)).bddAbove (Set.mem_image_of_mem _ hx)

theorem compact_support_height_radius (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (R : ℝ) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u : E) :
    compactSupportHeight K u ≤ ‖u‖ * R := by
  obtain ⟨q, hq, heq⟩ := compact_support_height_attained K hc hne u
  rw [← heq]
  exact (real_inner_le_norm u q).trans (mul_le_mul_of_nonneg_left (hR q hq) (norm_nonneg u))

theorem compact_support_height_lipschitz (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (R : ℝ) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u v : E) :
    compactSupportHeight K u ≤ compactSupportHeight K v + ‖u - v‖ * R := by
  obtain ⟨q, hq, heq⟩ := compact_support_height_attained K hc hne u
  have hv := compact_support_height_bound K hc hne v q hq
  have he : inner ℝ (u - v) q ≤ ‖u - v‖ * R :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hR q hq) (norm_nonneg _))
  rw [inner_sub_left] at he
  rw [← heq]
  linarith

theorem compact_support_height_unit_ball (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (hb : closedBall (0 : E) 1 ⊆ K) (u : E) (hu : ‖u‖ = 1) :
    1 ≤ compactSupportHeight K u := by
  have huK : u ∈ K := hb (by simpa only [mem_closedBall, dist_zero_right, hu] using (le_refl (1 : ℝ)))
  have huheight := compact_support_height_bound K hc hne u u huK
  simpa only [real_inner_self_eq_norm_sq, hu, one_pow] using huheight

/-- A compact convex body equals its actual unit supporting halfspaces.
Nearest-point separation discharges the converse. -/
theorem compact_convex_eq_support_halfspaces (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) :
    K = {x | ∀ u : E, ‖u‖ = 1 → inner ℝ u x ≤ compactSupportHeight K u} := by
  ext x
  constructor
  · intro hx u _
    exact compact_support_height_bound K hc hne u x hx
  · intro hx
    by_contra hnot
    obtain ⟨k, hk, u, _, hu, hgap, hsep, _⟩ := closest_support K hconv hc.isComplete hne x hnot
    obtain ⟨q, hq, hqheight⟩ := compact_support_height_attained K hc hne u
    have hheights : compactSupportHeight K u ≤ inner ℝ u k := by
      rw [← hqheight]
      exact hsep q hq
    have hxu := hx u hu
    linarith

theorem compact_support_height_nonnegative_smul (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (a : ℝ) (ha : 0 ≤ a) (u : E) :
    compactSupportHeight (a • K) u = a * compactSupportHeight K u := by
  have hca : IsCompact (a • K) := hc.image (continuous_const.smul continuous_id)
  have hnea : (a • K).Nonempty := hne.smul_set
  obtain ⟨q, hq, hqheight⟩ := compact_support_height_attained K hc hne u
  apply le_antisymm
  · obtain ⟨x, hx, hxheight⟩ := compact_support_height_attained (a • K) hca hnea u
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hxheight, inner_smul_right]
    exact mul_le_mul_of_nonneg_left (compact_support_height_bound K hc hne u y hy) ha
  · have haq : a • q ∈ a • K := Set.smul_mem_smul_set hq
    have hb := compact_support_height_bound (a • K) hca hnea u (a • q) haq
    simpa only [inner_smul_right, hqheight] using hb

end CompactSupport

section FiniteNetApproximation

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] in
theorem finite_halfspace_sphere_net_norm_bound (n : ι → E) (h : ι → ℝ)
    (ε R : ℝ) (hεsmall : ε ≤ 1 / 2) (hR : 0 ≤ R)
    (hheight : ∀ i, h i ≤ R)
    (hnet : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - n i‖ < ε)
    (x : E) (hx : x ∈ finiteHalfspaceSet n h) : ‖x‖ ≤ 2 * R := by
  by_cases hx0 : x = 0
  · simp [hx0, hR]
  have hnz : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnz), inv_mul_cancel₀ (ne_of_gt hnz)]
  have hux : inner ℝ u x = ‖x‖ := by
    dsimp [u]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hnz), one_mul]
  obtain ⟨i, hi⟩ := hnet u hu
  have herr : inner ℝ (u - n i) x ≤ ε * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg x))
  rw [inner_sub_left, hux] at herr
  have hni : inner ℝ (n i) x ≤ R := (hx i).trans (hheight i)
  have heps := mul_le_mul_of_nonneg_right hεsmall (norm_nonneg x)
  nlinarith

omit [Fintype ι] in
theorem finite_support_net_direction_bound (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (R : ℝ) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (n : ι → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hnet : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - n i‖ < ε)
    (x : E) (hx : x ∈ finiteHalfspaceSet n (fun i => compactSupportHeight K (n i)))
    (hxR : ‖x‖ ≤ 2 * R) (u : E) (hu : ‖u‖ = 1) :
    inner ℝ u x ≤ compactSupportHeight K u + 3 * ε * R := by
  obtain ⟨i, hi⟩ := hnet u hu
  have hRi : 0 ≤ R := (norm_nonneg _).trans (hR _ (Classical.choose_spec hne))
  have hheight := compact_support_height_lipschitz K hc hne R hR (n i) u
  have hinorm : ‖n i - u‖ ≤ ε := by rw [norm_sub_rev]; exact hi.le
  have hmheight := mul_le_mul_of_nonneg_right hinorm hRi
  have herr : inner ℝ (u - n i) x ≤ ε * ‖x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hi.le (norm_nonneg x))
  rw [inner_sub_left] at herr
  have hmx := mul_le_mul_of_nonneg_left hxR hε
  linarith [hx i]

omit [Fintype ι] in
theorem finite_support_net_subset_dilation (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K)
    (R : ℝ) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (n : ι → E) (hn : ∀ i, ‖n i‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 2)
    (hnet : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - n i‖ < ε) :
    finiteHalfspaceSet n (fun i => compactSupportHeight K (n i)) ⊆ (1 + 3 * ε * R) • K := by
  have hRi : 0 ≤ R := (norm_nonneg _).trans (hR _ (Classical.choose_spec hne))
  have ha : 0 ≤ 1 + 3 * ε * R := by positivity
  have hac : IsCompact ((1 + 3 * ε * R) • K) := hc.image (continuous_const.smul continuous_id)
  have hane : ((1 + 3 * ε * R) • K).Nonempty := hne.smul_set
  have haconv : Convex ℝ ((1 + 3 * ε * R) • K) :=
    hconv.linear_image (LinearMap.lsmul ℝ E (1 + 3 * ε * R))
  intro x hx
  rw [compact_convex_eq_support_halfspaces _ hac hane haconv]
  intro u hu
  rw [compact_support_height_nonnegative_smul K hc hne _ ha]
  have hheight : ∀ i, compactSupportHeight K (n i) ≤ R := by
    intro i
    simpa only [hn i, one_mul] using compact_support_height_radius K hc hne R hR (n i)
  have hxR := finite_halfspace_sphere_net_norm_bound n _ ε R hεsmall hRi hheight hnet x hx
  have hdir := finite_support_net_direction_bound K hc hne R hR n ε hε.le hnet x hx hxR u hu
  have hunit := compact_support_height_unit_ball K hc hne hb u hu
  have hprod := mul_le_mul_of_nonneg_left hunit (show 0 ≤ 3 * ε * R by positivity)
  nlinarith

end FiniteNetApproximation

section SupportingApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem finite_halfspace_closed {ι : Type*} (n : ι → E) (h : ι → ℝ) :
    IsClosed (finiteHalfspaceSet n h) := by
  have heq : finiteHalfspaceSet n h = ⋂ i, {x : E | inner ℝ (n i) x ≤ h i} := by
    ext x
    simp [finiteHalfspaceSet]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le
    (show Continuous (fun x : E => inner ℝ (n i) x) from continuous_const.inner continuous_id)
    continuous_const)

omit [FiniteDimensional ℝ E] in
theorem convex_nonnegative_dilation_mono (K : Set E) (hconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) : a • K ⊆ b • K := by
  rintro x ⟨q, hq, rfl⟩
  refine ⟨(a / b) • q, hconv.smul_mem_of_zero_mem h0 hq
    ⟨div_nonneg ha hb.le, (div_le_one hb).mpr hab⟩, ?_⟩
  change b • ((a / b) • q) = a • q
  rw [smul_smul, mul_comm b (a / b), div_mul_cancel₀ a hb.ne']

/-- Actual finite supporting-halfspace approximation with no supplied
polytope representation: the unit normals are an actual finite sphere net,
the heights are actual supporting heights, and compactness and both body
inclusions are proved. The index is the finite normal set itself, so its
normal map is literally injective. -/
theorem exists_finite_support_halfspace_approximation (K : Set E) (hc : IsCompact K)
    (hconv : Convex ℝ K) (hb : closedBall (0 : E) 1 ⊆ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset E,
      (∀ u : s, ‖(u : E)‖ = 1 ∧ 0 < compactSupportHeight K (u : E)) ∧
      Function.Injective (fun u : s => (u : E)) ∧
      IsCompact (finiteHalfspaceSet (fun u : s => (u : E))
        (fun u : s => compactSupportHeight K (u : E))) ∧
      K ⊆ finiteHalfspaceSet (fun u : s => (u : E))
        (fun u : s => compactSupportHeight K (u : E)) ∧
      finiteHalfspaceSet (fun u : s => (u : E))
        (fun u : s => compactSupportHeight K (u : E)) ⊆ (1 + δ) • K := by
  classical
  have h0 : (0 : E) ∈ K := hb (by simp)
  have hne : K.Nonempty := ⟨0, h0⟩
  obtain ⟨R, hRpos, hKR⟩ := hc.isBounded.subset_closedBall_lt 1 (0 : E)
  have hR : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hKR hx
  let ε : ℝ := min (δ / (3 * R)) (1 / 4)
  have hε : 0 < ε := lt_min (div_pos hδ (by positivity)) (by norm_num)
  have hεsmall : ε ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hεR : 3 * ε * R ≤ δ := by
    have he := (le_div_iff₀ (show 0 < 3 * R by positivity)).mp (min_le_left (δ / (3 * R)) (1 / 4))
    change ε * (3 * R) ≤ δ at he
    nlinarith
  obtain ⟨t, htsphere, htfinite, htcover⟩ := (isCompact_sphere (0 : E) (1 : ℝ)).finite_cover_balls hε
  let s : Finset E := htfinite.toFinset
  let n : s → E := fun u => (u : E)
  have hn : ∀ i : s, ‖n i‖ = 1 := by
    intro i
    have hit : (i : E) ∈ t := htfinite.mem_toFinset.mp i.2
    simpa only [mem_sphere, dist_zero_right] using htsphere hit
  have hnet : ∀ u : E, ‖u‖ = 1 → ∃ i : s, ‖u - n i‖ < ε := by
    intro u hu
    have hut : u ∈ ⋃ v ∈ t, ball v ε := htcover (by simpa only [mem_sphere, dist_zero_right] using hu)
    obtain ⟨v, hv, huv⟩ := Set.mem_iUnion.mp hut |>.imp fun v => Set.mem_iUnion.mp
    refine ⟨⟨v, htfinite.mem_toFinset.mpr hv⟩, ?_⟩
    simpa only [mem_ball, dist_eq_norm] using huv
  have hPa := finite_support_net_subset_dilation K hc hne hconv hb R hR n hn ε hε hεsmall hnet
  have hPcompact : IsCompact (finiteHalfspaceSet n (fun i => compactSupportHeight K (n i))) :=
    (hc.image (continuous_const.smul continuous_id)).of_isClosed_subset
      (finite_halfspace_closed n _) hPa
  refine ⟨s, ?_, Subtype.val_injective, hPcompact, ?_, ?_⟩
  · intro u
    have hunit := hn u
    exact ⟨hunit, (by norm_num : (0 : ℝ) < 1).trans_le
      (compact_support_height_unit_ball K hc hne hb (n u) hunit)⟩
  · intro x hx i
    exact compact_support_height_bound K hc hne (n i) x hx
  · exact hPa.trans (convex_nonnegative_dilation_mono K hconv h0
      (1 + 3 * ε * R) (1 + δ) (by positivity) (by linarith) (by linarith))

end SupportingApproximation
end Entry005
