import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace MinimaxProfile

/-- Exact finite feasible Bell dimensions, with the actual integer floors. -/
def feasibleDimensions (a b r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 a).filter (fun d => r ≤ (a / d) * (b / d))

theorem one_mem_feasible {a b r : ℕ} (ha : 0 < a) (hr : r ≤ a * b) :
    1 ∈ feasibleDimensions a b r := by
  simp only [feasibleDimensions, Finset.mem_filter, Finset.mem_Icc, Nat.div_one]
  exact ⟨⟨le_rfl, ha⟩, hr⟩

noncomputable def packingDimension (a b r : ℕ) (ha : 0 < a) (hr : r ≤ a * b) : ℕ :=
  (feasibleDimensions a b r).max' ⟨1, one_mem_feasible ha hr⟩

theorem packingDimension_mem {a b r : ℕ} (ha : 0 < a) (hr : r ≤ a * b) :
    packingDimension a b r ha hr ∈ feasibleDimensions a b r :=
  Finset.max'_mem _ _

theorem packingDimension_properties {a b r : ℕ} (ha : 0 < a) (hr : r ≤ a * b) :
    0 < packingDimension a b r ha hr ∧
    packingDimension a b r ha hr ≤ a ∧
    r ≤ (a / packingDimension a b r ha hr) * (b / packingDimension a b r ha hr) := by
  have h := packingDimension_mem ha hr
  simpa only [feasibleDimensions, Finset.mem_filter, Finset.mem_Icc, and_assoc,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using h

theorem feasible_le_packingDimension {a b r d : ℕ}
    (ha : 0 < a) (hr : r ≤ a * b) (hd : 0 < d) (hda : d ≤ a)
    (hf : r ≤ (a / d) * (b / d)) :
    d ≤ packingDimension a b r ha hr := by
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,hda⟩,hf⟩

/-- No feasible integer packing exceeds the continuous collision budget. -/
theorem feasible_dimension_square_bound {a b r d : ℕ}
    (hf : r ≤ (a / d) * (b / d)) : r * d ^ 2 ≤ a * b := by
  have ha := Nat.div_mul_le_self a d
  have hb := Nat.div_mul_le_self b d
  calc
    r * d ^ 2 ≤ ((a / d) * (b / d)) * d ^ 2 := Nat.mul_le_mul_right _ hf
    _ = ((a / d) * d) * ((b / d) * d) := by ring
    _ ≤ a * b := Nat.mul_le_mul ha hb

theorem cast_div_lower (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d - 1 ≤ ((a / d : ℕ) : ℝ) := by
  have hmul : (a : ℝ) < (d : ℝ) * (((a / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ a hd
  have h : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).2 (by simpa [mul_comm] using hmul)
  linarith

/-- A finite floor-packing criterion. The slack q=w/a+w/b accounts for
both integer quotients. Choosing d<=w/(1+q) suffices, without ignoring ranks. -/
theorem feasible_of_collision_slack {a b r d : ℕ} {w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hda : d ≤ a) (hdb : d ≤ b)
    (hw : 0 < w) (hbudget : (r : ℝ) * w ^ 2 = (a : ℝ) * b)
    (hsmall : (d : ℝ) ≤ w / (1 + (w / a + w / b))) :
    r ≤ (a / d) * (b / d) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let q := w / a + w / b
  have hq : 0 ≤ q := add_nonneg (div_nonneg hw.le haR.le) (div_nonneg hw.le hbR.le)
  have hs : (d : ℝ) * (1 + q) ≤ w := (le_div_iff₀ (by positivity : 0 < 1+q)).mp hsmall
  have hwd : (d : ℝ) ≤ w := by nlinarith
  have hE : 0 ≤ w ^ 2 - (d : ℝ) * w * q - (d : ℝ)^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ w + d by positivity)
    have hqterm := mul_nonneg (sq_nonneg (d : ℝ)) hq
    nlinarith
  have hqmul : (r : ℝ) * w * q = (a : ℝ) + b := by
    dsimp only [q]
    field_simp
    nlinarith [hbudget]
  have hkey : (r : ℝ) * (d : ℝ)^2 ≤ ((a : ℝ) - d) * ((b : ℝ) - d) := by
    have hprod := mul_nonneg (show 0 ≤ (r : ℝ) by positivity) hE
    have he := congrArg (fun t : ℝ => t * d) hqmul
    nlinarith [sq_nonneg (d : ℝ)]
  have hreal : (r : ℝ) ≤ ((a : ℝ) / d - 1) * ((b : ℝ) / d - 1) := by
    have he : ((a : ℝ) / d - 1) * ((b : ℝ) / d - 1) =
        ((a : ℝ) - d) * ((b : ℝ) - d) / (d : ℝ)^2 := by
      field_simp
      <;> ring
    rw [he]
    exact (le_div_iff₀ (sq_pos_of_pos hdR)).mpr hkey
  have hfa := cast_div_lower a d hd
  have hfb := cast_div_lower b d hd
  have hxa : 0 ≤ (a : ℝ) / d - 1 := by
    have h : (1 : ℝ) ≤ (a : ℝ) / d := (le_div_iff₀ hdR).2
      (by simpa only [one_mul] using (show (d : ℝ) ≤ a by exact_mod_cast hda))
    linarith
  have hmul : ((a : ℝ) / d - 1) * ((b : ℝ) / d - 1) ≤
      ((a / d : ℕ) : ℝ) * ((b / d : ℕ) : ℝ) := by
    calc
      _ ≤ ((a : ℝ) / d - 1) * ((b / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hfb hxa
      _ ≤ _ := mul_le_mul_of_nonneg_right hfa (by positivity)
  exact_mod_cast hreal.trans hmul

theorem feasible_dimension_real_bound {a b r d : ℕ} {w : ℝ}
    (hr : 0 < r) (hw : 0 ≤ w)
    (hbudget : (r : ℝ) * w ^ 2 = (a : ℝ) * b)
    (hf : r ≤ (a / d) * (b / d)) : (d : ℝ) ≤ w := by
  have h := feasible_dimension_square_bound hf
  have hR : (r : ℝ) * (d : ℝ)^2 ≤ (a : ℝ) * b := by exact_mod_cast h
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : (d : ℝ)^2 ≤ w^2 := by
    by_contra hsq
    have hp := mul_pos hrR (sub_pos.mpr (lt_of_not_ge hsq))
    nlinarith
  exact (sq_le_sq₀ (by positivity) hw).mp hs

end MinimaxProfile
