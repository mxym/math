import Entry005.Cap
import Entry005.BallVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Metric MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual image convex body under the orthogonal projection into a subspace. -/
def projectBody (U : Submodule ℝ E) (K : ConvexBody E) : ConvexBody U where
  carrier := U.orthogonalProjectionOnto '' (K : Set E)
  convex' := K.convex.linear_image U.orthogonalProjectionOnto.toLinearMap
  isCompact' := K.isCompact.image U.orthogonalProjectionOnto.continuous
  nonempty' := K.nonempty.image U.orthogonalProjectionOnto

theorem project_body_mono (U : Submodule ℝ E) (K P : ConvexBody E) (h : K ≤ P) :
    projectBody U K ≤ projectBody U P := Set.image_mono h

theorem project_body_unit_ball (U : Submodule ℝ E) (K : ConvexBody E)
    (hball : closedBall (0 : E) 1 ⊆ K) :
    closedBall (0 : U) 1 ⊆ projectBody U K := by
  intro x hx
  have hxE : (x : E) ∈ closedBall (0 : E) 1 := by
    simpa [mem_closedBall, dist_zero_right] using hx
  exact ⟨x, hball hxE, U.orthogonalProjectionOnto_mem_subspace_eq_self x⟩

theorem project_body_outer_ball (U : Submodule ℝ E) (P : ConvexBody E) (M : ℝ)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M) :
    (projectBody U P : Set U) ⊆ closedBall (0 : U) M := by
  rintro x ⟨y, hy, rfl⟩
  have hyM : ‖y‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hPM hy
  simpa [mem_closedBall, dist_zero_right] using
    (U.norm_orthogonalProjectionOnto_apply_le y).trans hyM

/-- A normal in the target subspace sees exactly the same linear functional
before and after projection. -/
theorem inner_project (U : Submodule ℝ E) (n : E) (hnU : n ∈ U) (x : E) :
    inner ℝ (⟨n, hnU⟩ : U) (U.orthogonalProjectionOnto x) = inner ℝ n x := by
  change inner ℝ n (U.starProjection x) = inner ℝ n x
  have h := U.starProjection_inner_eq_zero x n hnU
  rw [inner_sub_left] at h
  rw [real_inner_comm (U.starProjection x) n, real_inner_comm x n]
  linarith

/-- There is a unit projection direction perpendicular to a given unit normal
in every real inner product space of dimension at least two. -/
theorem exists_perpendicular_unit (hd : 2 ≤ Module.finrank ℝ E) (n : E) (hn : ‖n‖ = 1) :
    ∃ u : E, ‖u‖ = 1 ∧ inner ℝ u n = 0 := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hdim := (ℝ ∙ n).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hn0] at hdim
  have hpos : 0 < Module.finrank ℝ (ℝ ∙ n)ᗮ := by omega
  let : Nontrivial (ℝ ∙ n)ᗮ := Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : (ℝ ∙ n)ᗮ)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvE : ‖(v : E)‖ ≠ 0 := hvpos.ne'
  let u : E := (‖v‖⁻¹ : ℝ) • (v : E)
  refine ⟨u, ?_, ?_⟩
  · simp [u, norm_smul, hvE]
  · have horth : inner ℝ (v : E) n = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
    simp [u, inner_smul_left, horth]

/-- The hyperplane normal to a unit vector has precisely codimension one. -/
theorem hyperplane_dimension (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu0] at hdim
  omega

variable [MeasurableSpace E] [BorelSpace E]

/-- Intrinsic projected volume; the measure is the canonical Euclidean volume
on the target subspace, never ambient d-dimensional volume of a hyperplane. -/
def projectedVolume (U : Submodule ℝ E) (K : ConvexBody E) : ENNReal :=
  volume (projectBody U K : Set U)

/-- The gap-preserving projection followed by the actual cap-measure theorem. -/
theorem projection_cap_gain (K P : ConvexBody E) (U : Submodule ℝ E)
    (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q k n : E) (hq : q ∈ P) (hn : ‖n‖ = 1) (hnU : n ∈ U)
    (hs : 0 < ‖q - k‖) (hsM : ‖q - k‖ ≤ M)
    (hgap : inner ℝ n q - inner ℝ n k = ‖q - k‖)
    (hsep : ∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) :
    projectedVolume U K +
      ENNReal.ofReal ((‖q - k‖ / (2 * (M + 1))) ^ Module.finrank ℝ U) *
      volume (closedBall (0 : U) 1) ≤ projectedVolume U P := by
  let nU : U := ⟨n, hnU⟩
  let qU := U.orthogonalProjectionOnto q
  let kU := U.orthogonalProjectionOnto k
  have hqU : qU ∈ projectBody U P := ⟨q, hq, rfl⟩
  have hqM : ‖q‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hPM hq
  have hqUM : ‖qU‖ ≤ M := (U.norm_orthogonalProjectionOnto_apply_le q).trans hqM
  have hgapU : inner ℝ nU qU - inner ℝ nU kU = ‖q - k‖ := by
    simp only [nU, qU, kU, inner_project U n hnU]
    exact hgap
  have hsepU : ∀ x ∈ projectBody U K, inner ℝ nU x ≤ inner ℝ nU kU := by
    rintro x ⟨y, hy, rfl⟩
    simpa only [nU, kU, inner_project U n hnU] using hsep y hy
  exact cap_measure_gain volume (projectBody U K : Set U) (projectBody U P : Set U)
    nU qU kU M ‖q - k‖ (project_body_mono U K P hKP)
    (projectBody U P).convex
    ((project_body_unit_ball U K hball).trans (project_body_mono U K P hKP))
    hqU hn hM hqUM hs hsM hgapU hsepU

/-- The explicit cube constant: a supporting gap s yields a projected volume
gain of at least (s/(m(M+1)))^m, where m is the true target dimension. -/
theorem projection_cap_cube_gain (K P : ConvexBody E) (U : Submodule ℝ E)
    (hm : 1 ≤ Module.finrank ℝ U) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q k n : E) (hq : q ∈ P) (hn : ‖n‖ = 1) (hnU : n ∈ U)
    (hs : 0 < ‖q - k‖) (hsM : ‖q - k‖ ≤ M)
    (hgap : inner ℝ n q - inner ℝ n k = ‖q - k‖)
    (hsep : ∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) :
    projectedVolume U K +
      ENNReal.ofReal ((‖q - k‖ / ((Module.finrank ℝ U : ℝ) * (M + 1))) ^
        Module.finrank ℝ U) ≤ projectedVolume U P := by
  have ht : 0 ≤ ‖q - k‖ / (2 * (M + 1)) := by positivity
  have hmpos : (0 : ℝ) < Module.finrank ℝ U := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have heq : ‖q - k‖ / (2 * (M + 1)) * (2 / (Module.finrank ℝ U : ℝ)) =
      ‖q - k‖ / ((Module.finrank ℝ U : ℝ) * (M + 1)) := by
    field_simp
  have hvol := unit_ball_cube (E := U) hm
  have hprod := mul_le_mul_right hvol
    (ENNReal.ofReal ((‖q - k‖ / (2 * (M + 1))) ^ Module.finrank ℝ U))
  rw [← ENNReal.ofReal_mul (pow_nonneg ht _), ← mul_pow, heq] at hprod
  exact (add_le_add_right hprod (projectedVolume U K)).trans
    (projection_cap_gain K P U M hM hball hKP hPM q k n hq hn hnU hs hsM hgap hsep)

/-- The complete geometric projection-cap lower bound, for any point outside
the inner body.  The nearest point, supporting normal and codimension-one
projection direction are all produced by the proof. -/
theorem exists_projection_cap (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q : E) (hq : q ∈ P) (hqK : q ∉ K) :
    ∃ k ∈ K, ∃ u : E, ‖u‖ = 1 ∧
      (∀ x ∈ K, ‖q - k‖ ≤ ‖q - x‖) ∧
      projectedVolume (ℝ ∙ u)ᗮ K +
        ENNReal.ofReal ((‖q - k‖ / (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (M + 1))) ^
          (Module.finrank ℝ E - 1)) ≤ projectedVolume (ℝ ∙ u)ᗮ P := by
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
  have h := projection_cap_cube_gain K P (ℝ ∙ u)ᗮ hm M hM hball hKP hPM
    q k n hq hn hnU hs hsM hgap hsep
  simpa only [hdim] using h

/-- Full projection-deficit to Hausdorff conversion with the written constant
`(d-1)(M+1)` and exponent `1/(d-1)`.  The hypothesis is a bound on actual
intrinsic projection volumes. No cap inequality is assumed. -/
theorem hausdorff_from_projection_deficit (hd : 2 ≤ Module.finrank ℝ E)
    (K P : ConvexBody E) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (hdef : ∀ u : E, ‖u‖ = 1 →
      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -
        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η) :
    Metric.hausdorffDist (K : Set E) (P : Set E) ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (M + 1) *
        η ^ (1 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) := by
  let m := Module.finrank ℝ E - 1
  let C : ℝ := (m : ℝ) * (M + 1)
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
      exists_projection_cap hd K P M hM hball hKP hPM q hq hqK
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

end Entry005
