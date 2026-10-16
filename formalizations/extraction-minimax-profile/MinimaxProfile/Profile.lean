import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! Finite target-uniform scalar comparison used after physical bounds.
This module does not assume any Schur or ensemble identities. -/
namespace MinimaxProfile

noncomputable def profile (w K : ℝ) : ℝ := min 1 (w / K)

theorem profile_pos {w K : ℝ} (hw : 0 < w) (hK : 0 < K) :
    0 < profile w K := lt_min zero_lt_one (div_pos hw hK)

theorem profile_le_one (w K : ℝ) : profile w K ≤ 1 := min_le_left _ _

theorem profile_mono {u v K : ℝ} (h : u ≤ v) (hK : 0 ≤ K) :
    profile u K ≤ profile v K := min_le_min_left _ (div_le_div_of_nonneg_right h hK)

/-- Scaling the available target size down loses no more than the same factor,
uniformly in the requested target. -/
theorem profile_scale_lower {u w K : ℝ}
    (hu : 0 ≤ u) (huw : u ≤ w) (hw : 0 < w) (hK : 0 < K) :
    (u / w) * profile w K ≤ profile u K := by
  unfold profile
  apply le_min
  · have hratio : u / w ≤ 1 := (div_le_one hw).2 huw
    exact (mul_le_mul_of_nonneg_left (min_le_left 1 (w / K)) (div_nonneg hu hw.le)).trans
      (by simpa using hratio)
  · calc
      (u / w) * min 1 (w / K) ≤ (u / w) * (w / K) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (div_nonneg hu hw.le)
      _ = u / K := by field_simp

/-- Scaling up the collision budget changes every relative target profile by
at most the same factor. -/
theorem profile_scale_upper {η w K : ℝ}
    (hη : 1 ≤ η) (hw : 0 < w) (hK : 0 < K) :
    profile (η * w) K ≤ η * profile w K := by
  unfold profile
  by_cases h : w / K ≤ 1
  · rw [min_eq_right h]
    calc
      min 1 (η * w / K) ≤ η * w / K := min_le_right _ _
      _ = η * (w / K) := by ring
  · rw [min_eq_left (le_of_not_ge h), mul_one]
    exact (min_le_left _ _).trans hη

/-- The precise finite relative-error bound, valid for every positive real
target K. The physical and ensemble bounds are supplied by separate modules. -/
theorem relative_profile_bound {d w η K F : ℝ}
    (hd : 0 ≤ d) (hdw : d ≤ w) (hw : 0 < w) (hη : 1 ≤ η) (hK : 0 < K)
    (hlo : profile d K ≤ F) (hhi : F ≤ profile (η * w) K) :
    |F / profile w K - 1| ≤ max (1 - d / w) (η - 1) := by
  have hp := profile_pos hw hK
  have hl : d / w ≤ F / profile w K := by
    apply (le_div_iff₀ hp).2
    exact (profile_scale_lower hd hdw hw hK).trans hlo
  have hh : F / profile w K ≤ η := by
    apply (div_le_iff₀ hp).2
    exact hhi.trans (profile_scale_upper hη hw hK)
  apply abs_le.mpr
  constructor
  · have h := le_max_left (1 - d / w) (η - 1)
    linarith
  · exact (by linarith : F / profile w K - 1 ≤ η - 1).trans (le_max_right _ _)

/-- The supremum is over every positive integer target, with no rate restriction. -/
noncomputable def worstRelativeError (F : ℕ → ℝ) (w : ℝ) : ℝ :=
  sSup (Set.range (fun j : ℕ => |F (j + 1) / profile w (j + 1) - 1|))

theorem worstRelativeError_bounds {d w η : ℝ} {F : ℕ → ℝ}
    (hd : 0 ≤ d) (hdw : d ≤ w) (hw : 0 < w) (hη : 1 ≤ η)
    (hlo : ∀ K : ℕ, 0 < K → profile d K ≤ F K)
    (hhi : ∀ K : ℕ, 0 < K → F K ≤ profile (η * w) K) :
    0 ≤ worstRelativeError F w ∧
    worstRelativeError F w ≤ max (1 - d / w) (η - 1) := by
  have hb (j : ℕ) : |F (j + 1) / profile w (j + 1) - 1| ≤
      max (1 - d / w) (η - 1) :=
    relative_profile_bound hd hdw hw hη (by positivity)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hlo (j + 1) (by omega))
      (by simpa only [Nat.cast_add, Nat.cast_one] using hhi (j + 1) (by omega))
  have hbd : BddAbove (Set.range (fun j : ℕ => |F (j + 1) / profile w (j + 1) - 1|)) :=
    ⟨max (1 - d / w) (η - 1), by rintro _ ⟨j,rfl⟩; exact hb j⟩
  constructor
  · exact (abs_nonneg _).trans (le_csSup hbd ⟨0,rfl⟩)
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨j,rfl⟩; exact hb j)

/-- General limit synthesis after the physical finite bounds and the genuine
support/moment limits have been established. No convergence is inferred from
an unchecked informal typicality premise. -/
theorem target_uniform_relative_limit
    {d w η : ℕ → ℝ} {F : ℕ → ℕ → ℝ}
    (hd : ∀ k, 0 ≤ d k) (hdw : ∀ k, d k ≤ w k)
    (hw : ∀ k, 0 < w k) (hη : ∀ k, 1 ≤ η k)
    (hlo : ∀ k K : ℕ, 0 < K → profile (d k) K ≤ F k K)
    (hhi : ∀ k K : ℕ, 0 < K → F k K ≤ profile (η k * w k) K)
    (hratio : Filter.Tendsto (fun k => d k / w k) Filter.atTop (nhds 1))
    (heta : Filter.Tendsto η Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun k => worstRelativeError (F k) (w k))
      Filter.atTop (nhds 0) := by
  have hb (k : ℕ) := worstRelativeError_bounds (hd k) (hdw k) (hw k) (hη k)
    (hlo k) (hhi k)
  apply squeeze_zero (fun k => (hb k).1) (fun k => (hb k).2)
  have hh := (Filter.Tendsto.const_sub 1 hratio).max
    (heta.sub_const 1)
  simpa using hh

end MinimaxProfile
