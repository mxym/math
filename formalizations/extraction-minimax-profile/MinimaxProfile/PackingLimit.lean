import MinimaxProfile.IntegerPacking
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
namespace MinimaxProfile

/-- Explicit finite lower and upper bounds for the optimal integer packing.
The linear slack q is sufficient; no real rank replaces the original r. -/
theorem packing_ratio_bounds {a b r : ℕ} {w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hrab : r ≤ a * b)
    (hw : 0 < w) (hwa : w ≤ a) (hwb : w ≤ b)
    (hbudget : (r : ℝ) * w^2 = (a : ℝ) * b)
    (hlarge : 1 ≤ w / (1 + (w / a + w / b))) :
    1 / (1 + (w / a + w / b)) - 1 / w ≤
      (packingDimension a b r ha hrab : ℝ) / w ∧
    (packingDimension a b r ha hrab : ℝ) / w ≤ 1 := by
  let q := w / a + w / b
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let d : ℕ := ⌊w / (1+q)⌋₊
  have hd : 0 < d := Nat.floor_pos.mpr hlarge
  have hsmall : (d : ℝ) ≤ w / (1+q) := Nat.floor_le (by positivity)
  have hdmul : (d : ℝ) * (1+q) ≤ w :=
    (le_div_iff₀ (by positivity : 0 < 1+q)).mp hsmall
  have hdw : (d : ℝ) ≤ w := by nlinarith [show (0 : ℝ) ≤ d by positivity]
  have hda : d ≤ a := by exact_mod_cast hdw.trans hwa
  have hdb : d ≤ b := by exact_mod_cast hdw.trans hwb
  have hf := feasible_of_collision_slack ha hb hd hda hdb hw hbudget hsmall
  have hmax := feasible_le_packingDimension ha hrab hd hda hf
  constructor
  · have hfloor : w / (1+q) - 1 ≤ (packingDimension a b r ha hrab : ℝ) := by
      exact (Nat.sub_one_lt_floor _).le.trans (by exact_mod_cast hmax)
    have h := div_le_div_of_nonneg_right hfloor hw.le
    have he : (w / (1+q) - 1) / w = 1 / (1+q) - 1/w := by
      field_simp
      <;> ring
    simpa only [he] using h
  · exact (div_le_one hw).mpr (feasible_dimension_real_bound hr hw.le hbudget
      (packingDimension_properties ha hrab).2.2)

/-- The exact integer packing asymptotic in the entropy-limited regime, with
both local quotient losses controlled. No representation-theory inputs enter. -/
theorem packing_ratio_tendsto
    {a b r : ℕ → ℕ} {w : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (hr : ∀ k, 0 < r k) (hrab : ∀ k, r k ≤ a k * b k)
    (hw : ∀ k, 0 < w k)
    (hbudget : ∀ k, (r k : ℝ) * w k^2 = (a k : ℝ) * b k)
    (hwtop : Tendsto w atTop atTop)
    (hA : Tendsto (fun k => w k / a k) atTop (nhds 0))
    (hB : Tendsto (fun k => w k / b k) atTop (nhds 0)) :
    Tendsto (fun k => (packingDimension (a k) (b k) (r k) (ha k) (hrab k) : ℝ) / w k)
      atTop (nhds 1) := by
  let q := fun k => w k / a k + w k / b k
  have hq0 : Tendsto q atTop (nhds 0) := by simpa using hA.add hB
  have hq (k : ℕ) : 0 ≤ q k := by
    dsimp only [q]
    have haR : (0 : ℝ) < a k := by exact_mod_cast ha k
    have hbR : (0 : ℝ) < b k := by exact_mod_cast hb k
    exact add_nonneg (div_nonneg (hw k).le haR.le) (div_nonneg (hw k).le hbR.le)
  have hsmallA : ∀ᶠ k in atTop, w k ≤ a k := by
    have h := hA.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h] with k hk
    exact ((div_lt_one (by exact_mod_cast ha k : (0 : ℝ) < a k)).mp hk).le
  have hsmallB : ∀ᶠ k in atTop, w k ≤ b k := by
    have h := hB.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h] with k hk
    exact ((div_lt_one (by exact_mod_cast hb k : (0 : ℝ) < b k)).mp hk).le
  have hlarge : ∀ᶠ k in atTop, 1 ≤ w k / (1+q k) := by
    have hqsmall := hq0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    have hwlarge : ∀ᶠ k in atTop, (2 : ℝ) ≤ w k := hwtop.eventually_ge_atTop 2
    filter_upwards [hqsmall,hwlarge] with k hqk hwk
    apply (le_div_iff₀ (by positivity : 0 < 1+q k)).mpr
    linarith
  have hup (k : ℕ) :
      (packingDimension (a k) (b k) (r k) (ha k) (hrab k) : ℝ) / w k ≤ 1 :=
    (div_le_one (hw k)).mpr (feasible_dimension_real_bound (hr k) (hw k).le (hbudget k)
      (packingDimension_properties (ha k) (hrab k)).2.2)
  have hlow : ∀ᶠ k in atTop, 1 / (1+q k) - 1/w k ≤
      (packingDimension (a k) (b k) (r k) (ha k) (hrab k) : ℝ) / w k := by
    filter_upwards [hsmallA,hsmallB,hlarge] with k hak hbk hlargek
    exact (packing_ratio_bounds (ha k) (hb k) (hr k) (hrab k) (hw k) hak hbk (hbudget k) hlargek).1
  have hinv : Tendsto (fun k => 1 / w k) atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hwtop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hden : Tendsto (fun k => 1 + q k) atTop (nhds 1) := by
    simpa using hone.add hq0
  have hlowlim : Tendsto (fun k => 1 / (1+q k) - 1/w k) atTop (nhds 1) := by
    simpa using (hone.div hden (by norm_num : (1 : ℝ) ≠ 0)).sub hinv
  have herr : Tendsto (fun k => 1 -
      (packingDimension (a k) (b k) (r k) (ha k) (hrab k) : ℝ) / w k) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun k => sub_nonneg.mpr (hup k))
      (hlow.mono fun k hk => sub_le_sub_left hk 1)
    simpa using hone.sub hlowlim
  simpa using hone.sub herr

end MinimaxProfile
