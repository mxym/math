import Entry005.ProjectionCap
import Entry005.StrongBallVolume

/-!
An improved projection-cap estimate using an actual cube of side `2 / √m`.
The final theorem assumes an outer radius for the inner body only.  The outer
body is bounded using its actual Hausdorff distance before that distance is
estimated, avoiding an assumed or circular small outer-radius conclusion.
-/

noncomputable section

open Metric MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A genuine supporting gap gives the improved intrinsic projected-volume
gain, using the coordinate cube proved inside the Euclidean unit ball. -/
theorem projection_cap_sqrt_cube_gain (K P : ConvexBody E) (U : Submodule ℝ E)
    (hm : 1 ≤ Module.finrank ℝ U) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q k n : E) (hq : q ∈ P) (hn : ‖n‖ = 1) (hnU : n ∈ U)
    (hs : 0 < ‖q - k‖) (hsM : ‖q - k‖ ≤ M)
    (hgap : inner ℝ n q - inner ℝ n k = ‖q - k‖)
    (hsep : ∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) :
    projectedVolume U K +
      ENNReal.ofReal ((‖q - k‖ / (Real.sqrt (Module.finrank ℝ U : ℝ) * (M + 1))) ^
        Module.finrank ℝ U) ≤ projectedVolume U P := by
  have ht : 0 ≤ ‖q - k‖ / (2 * (M + 1)) := by positivity
  have hmpos : (0 : ℝ) < Module.finrank ℝ U := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hsqrt : 0 < Real.sqrt (Module.finrank ℝ U : ℝ) := Real.sqrt_pos.mpr hmpos
  have heq : ‖q - k‖ / (2 * (M + 1)) * (2 / Real.sqrt (Module.finrank ℝ U : ℝ)) =
      ‖q - k‖ / (Real.sqrt (Module.finrank ℝ U : ℝ) * (M + 1)) := by
    field_simp
  have hvol := unit_ball_sqrt_cube (E := U) hm
  have hprod := mul_le_mul_right hvol
    (ENNReal.ofReal ((‖q - k‖ / (2 * (M + 1))) ^ Module.finrank ℝ U))
  rw [← ENNReal.ofReal_mul (pow_nonneg ht _), ← mul_pow, heq] at hprod
  exact (add_le_add_right hprod (projectedVolume U K)).trans
    (projection_cap_gain K P U M hM hball hKP hPM q k n hq hn hnU hs hsM hgap hsep)

/-- The minimizing point, supporting normal and perpendicular projection
direction are all constructed from the actual nested convex bodies. -/
theorem exists_projection_sqrt_cap (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q : E) (hq : q ∈ P) (hqK : q ∉ K) :
    ∃ k ∈ K, ∃ u : E, ‖u‖ = 1 ∧
      (∀ x ∈ K, ‖q - k‖ ≤ ‖q - x‖) ∧
      projectedVolume (ℝ ∙ u)ᗮ K +
        ENNReal.ofReal ((‖q - k‖ / (Real.sqrt (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          (M + 1))) ^ (Module.finrank ℝ E - 1)) ≤ projectedVolume (ℝ ∙ u)ᗮ P := by
  obtain ⟨k, hk, n, hs, hn, hgap, hsep, hmin⟩ :=
    closest_support (K : Set E) K.convex K.isCompact.isComplete K.nonempty q hqK
  obtain ⟨u, hu, hun⟩ := exists_perpendicular_unit hd n hn
  have hnU : n ∈ (ℝ ∙ u)ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hun
  have hdim := hyperplane_dimension u hu
  have hm : 1 ≤ Module.finrank ℝ (ℝ ∙ u)ᗮ := by rw [hdim]; omega
  have h0 : (0 : E) ∈ K := hball (by simp)
  have hqM : ‖q‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hPM hq
  have hsM : ‖q - k‖ ≤ M := (by simpa using hmin 0 h0 : ‖q - k‖ ≤ ‖q‖).trans hqM
  refine ⟨k, hk, u, hu, hmin, ?_⟩
  have h := projection_cap_sqrt_cube_gain K P (ℝ ∙ u)ᗮ hm M hM hball hKP hPM
    q k n hq hn hnU hs hsM hgap hsep
  simpa only [hdim] using h

/-- Actual projection-volume deficits control the Hausdorff distance with
constant `√(d-1) (M+1)`, for a supplied outer radius of the outer body. -/
theorem hausdorff_from_projection_deficit_sqrt (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (hdef : ∀ u : E, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η) :
    Metric.hausdorffDist (K : Set E) (P : Set E) ≤
      Real.sqrt (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (M + 1) *
        η ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) := by
  let m := Module.finrank ℝ E - 1
  let C : ℝ := Real.sqrt (m : ℝ) * (M + 1)
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : 0 ≤ C * η ^ (1 / (m : ℝ)) := by positivity
  apply Metric.hausdorffDist_le_of_mem_dist hbound
  · intro x hx
    exact ⟨x, hKP hx, by simpa using hbound⟩
  · intro q hq
    by_cases hqK : q ∈ K
    · exact ⟨q, hqK, by simpa using hbound⟩
    obtain ⟨k, hk, u, hu, _hmin, hcap⟩ :=
      exists_projection_sqrt_cap hd K P M hM hball hKP hPM q hq hqK
    have hfinK : projectedVolume (ℝ ∙ u)ᗮ K ≠ ⊤ :=
      (projectBody (ℝ ∙ u)ᗮ K).isCompact.measure_lt_top.ne
    have hfinP : projectedVolume (ℝ ∙ u)ᗮ P ≠ ⊤ :=
      (projectBody (ℝ ∙ u)ᗮ P).isCompact.measure_lt_top.ne
    have hpow0 : 0 ≤ (‖q - k‖ / C) ^ m := pow_nonneg (by positivity) _
    have hsumfin : projectedVolume (ℝ ∙ u)ᗮ K +
        ENNReal.ofReal ((‖q - k‖ / C) ^ m) ≠ ⊤ := by
      exact ne_top_of_le_ne_top hfinP hcap
    have hcapR := (ENNReal.toReal_le_toReal hsumfin hfinP).mpr hcap
    rw [ENNReal.toReal_add hfinK ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpow0] at hcapR
    have hpow : (‖q - k‖ / C) ^ m ≤ η := by linarith [hdef u hu]
    have hroot : ‖q - k‖ / C ≤ η ^ (1 / (m : ℝ)) := by
      rw [one_div]
      apply (Real.le_rpow_inv_iff_of_pos (by positivity) hη hmR).mpr
      rw [Real.rpow_natCast]
      exact hpow
    have hgap : ‖q - k‖ ≤ C * η ^ (1 / (m : ℝ)) := by
      have h := (div_le_iff₀ hC).mp hroot
      simpa only [mul_comm] using h
    exact ⟨k, hk, by simpa [dist_eq_norm] using hgap⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A compact inner body supplies genuine nearest-point witnesses and hence
an outer-radius bound for every point of the other compact body.  Nesting is
unnecessary for this metric fact. -/
theorem body_outer_ball_from_hausdorff (K P : ConvexBody E) (R : ℝ)
    (hKR : (K : Set E) ⊆ closedBall (0 : E) R) :
    (P : Set E) ⊆ closedBall (0 : E)
      (R + Metric.hausdorffDist (K : Set E) (P : Set E)) := by
  have hfin : Metric.hausdorffEDist (P : Set E) (K : Set E) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded P.nonempty K.nonempty
      P.isCompact.isBounded K.isCompact.isBounded
  intro q hq
  obtain ⟨k, hk, hnearest⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty q
  have hnear : dist q k ≤ Metric.hausdorffDist (K : Set E) (P : Set E) := by
    rw [← hnearest, Metric.hausdorffDist_comm]
    exact Metric.infDist_le_hausdorffDist_of_mem hq hfin
  have hkR : ‖k‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hKR hk
  have hqnorm : ‖q‖ ≤ R + Metric.hausdorffDist (K : Set E) (P : Set E) := by
    calc
      ‖q‖ ≤ ‖k‖ + ‖q - k‖ := by simpa [norm_sub_rev] using norm_le_norm_add_norm_sub k q
      _ ≤ R + Metric.hausdorffDist (K : Set E) (P : Set E) :=
        add_le_add hkR (by simpa [dist_eq_norm] using hnear)
  simpa [mem_closedBall, dist_zero_right] using hqnorm

/-- The stronger cap endpoint: only the inner body has a supplied outer
radius.  The actual Hausdorff distance supplies the intermediate radius
`R+s`; the small-root gate then absorbs the term involving `s`. -/
theorem hausdorff_from_inner_radius_projection_deficit (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (R η : ℝ) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hKR : (K : Set E) ⊆ closedBall (0 : E) R)
    (hdef : ∀ u : E, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η)
    (hsmall : Real.sqrt (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
      η ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) ≤ 1 / 2) :
    Metric.hausdorffDist (K : Set E) (P : Set E) ≤
      2 * Real.sqrt (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (R + 1) *
        η ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) := by
  let s := Metric.hausdorffDist (K : Set E) (P : Set E)
  let β := Real.sqrt (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
    η ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  have hs : 0 ≤ s := Metric.hausdorffDist_nonneg
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβsmall : β ≤ 1 / 2 := hsmall
  have houter := body_outer_ball_from_hausdorff K P R hKR
  have hcap := hausdorff_from_projection_deficit_sqrt hd K P (R + s) η
    (add_nonneg hR hs) hη hball hKP houter hdef
  have hcap' : s ≤ β * (R + s + 1) := by
    convert hcap using 1
    dsimp [s, β]
    ring
  have hterm : β * s ≤ s / 2 := by nlinarith
  have hresult : s ≤ 2 * β * (R + 1) := by nlinarith
  convert hresult using 1
  dsimp [s, β]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A small actual Hausdorff distance yields the improved outer radius only
after the distance has been bounded. -/
theorem outer_ball_after_small_hausdorff (K P : ConvexBody E) (R : ℝ)
    (hKR : (K : Set E) ⊆ closedBall (0 : E) R)
    (hsmall : Metric.hausdorffDist (K : Set E) (P : Set E) ≤ 1) :
    (P : Set E) ⊆ closedBall (0 : E) (R + 1) := by
  exact (body_outer_ball_from_hausdorff K P R hKR).trans
    (Metric.closedBall_subset_closedBall (add_le_add (le_refl R) hsmall))

/-- Zero deficit in every intrinsic hyperplane projection forces equality
of the actual nested convex bodies. -/
theorem bodies_eq_of_zero_projection_deficit (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (R : ℝ) (hR : 0 ≤ R)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hKR : (K : Set E) ⊆ closedBall (0 : E) R)
    (hdef : ∀ u : E, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ 0) : K = P := by
  have hm : 0 < ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Module.finrank ℝ E - 1 by omega)
  have hroot : (0 : ℝ) ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) = 0 :=
    Real.zero_rpow (by positivity)
  have hbound := hausdorff_from_inner_radius_projection_deficit hd K P R 0 hR
    (le_refl 0) hball hKP hKR hdef (by simp only [hroot, mul_zero]; norm_num)
  have hzero : Metric.hausdorffDist (K : Set E) (P : Set E) = 0 := by
    simp only [hroot, mul_zero] at hbound
    exact le_antisymm hbound Metric.hausdorffDist_nonneg
  have hfin : Metric.hausdorffEDist (K : Set E) (P : Set E) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty P.nonempty
      K.isCompact.isBounded P.isCompact.isBounded
  exact SetLike.coe_injective
    ((K.isCompact.isClosed.hausdorffDist_zero_iff_eq P.isCompact.isClosed hfin).mp hzero)

end Entry005
