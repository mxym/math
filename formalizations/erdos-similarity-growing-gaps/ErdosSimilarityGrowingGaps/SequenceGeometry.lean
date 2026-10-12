import ErdosSimilarityGrowingGaps.RoutingActiveGeometry
import ErdosSimilarityGrowingGaps.Input
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

/-- The actual sampled power point, expressed at a logarithmic sample `Z.z m`. -/
noncomputable def sequencePoint (Z : LogScale) (m : ℕ) (C x : ℝ)
    (p : PowerParams s₀ s₁) : ℝ :=
  powerPoint (input Z m) C (x, p)

/-- Strict activation in the logarithmic coordinate of an actual sample. -/
def sequencePowerActivation (Z : LogScale) (m : ℕ) (k : ℤ) (u v : ℝ)
    (p : PowerParams s₀ s₁) : Prop :=
  u < p.1.1 * Z.z m - k ∧ p.1.1 * Z.z m - k < v

theorem input_rpow_eq (Z : LogScale) (m : ℕ) (s : ℝ) :
    (input Z m) ^ s = (2 : ℝ) ^ (-Z.z m * s) := by
  rw [input_eq_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem sequence_shifted_offset (Z : LogScale) (m : ℕ) (s t : ℝ) (k : ℤ) :
    t * (2 : ℝ) ^ k * (input Z m) ^ s =
      t * (2 : ℝ) ^ ((k : ℝ) - s * Z.z m) := by
  rw [input_rpow_eq]
  rw [← Real.rpow_intCast, mul_assoc, ← Real.rpow_add (by norm_num)]
  congr 2
  ring

theorem sequence_active_offset_lower
    (Z : LogScale) (s₀ s₁ x u v : ℝ) (m : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k u v p) :
    (2 : ℝ) ^ (-v) < sequencePoint Z m ((2 : ℝ) ^ k) x p - x := by
  have hpow : (2 : ℝ) ^ (-v) <
      (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hp.2])
  have hmul : (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) ≤
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) := by
    nlinarith [p.2.2.1, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
      ((k : ℝ) - p.1.1 * Z.z m)]
  have hoff : p.2.1 * (2 : ℝ) ^ k * (input Z m) ^ p.1.1 =
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) := by
    rw [sequence_shifted_offset]
  simpa only [sequencePoint, powerPoint, add_sub_cancel_left, hoff] using hpow.trans_le hmul

theorem sequence_active_point_range
    (Z : LogScale) (s₀ s₁ x u v : ℝ) (m : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k u v p) :
    x < sequencePoint Z m ((2 : ℝ) ^ k) x p ∧
      sequencePoint Z m ((2 : ℝ) ^ k) x p < x + (2 : ℝ) ^ (1 - u) := by
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num) p.2.2.1
  have hoff : 0 < p.2.1 * (2 : ℝ) ^ k * (input Z m) ^ p.1.1 := by
    exact mul_pos (mul_pos ht (zpow_pos (by norm_num) k))
      (Real.rpow_pos_of_pos (input_pos Z m) _)
  have hw : u < p.1.1 * Z.z m - k := hp.1
  have hsmall : (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) < (2 : ℝ) ^ (-u) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hbound : p.2.1 * (2 : ℝ) ^ k * (input Z m) ^ p.1.1 <
      (2 : ℝ) ^ (1 - u) := by
    rw [sequence_shifted_offset]
    calc
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) ≤
          2 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) :=
        mul_le_mul_of_nonneg_right p.2.2.2
          (Real.rpow_pos_of_pos (by norm_num) _).le
      _ < 2 * (2 : ℝ) ^ (-u) := mul_lt_mul_of_pos_left hsmall (by norm_num)
      _ = (2 : ℝ) ^ (1 - u) := by
        calc
          2 * (2 : ℝ) ^ (-u) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-u) := by
            rw [Real.rpow_one]
          _ = (2 : ℝ) ^ ((1 : ℝ) + -u) := (Real.rpow_add (by norm_num) _ _).symm
          _ = (2 : ℝ) ^ (1 - u) := by congr 1
  change x < x + _ ∧ x + _ < x + _
  exact ⟨by linarith, by linarith⟩

theorem sequence_active_point_short
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (m : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k (u : ℝ) ((u : ℝ) + ell) p) :
    x < sequencePoint Z m ((2 : ℝ) ^ k) x p ∧
      sequencePoint Z m ((2 : ℝ) ^ k) x p - x < 1 / 8 := by
  have hr := sequence_active_point_range Z s₀ s₁ x (u : ℝ) ((u : ℝ) + ell) m k p hp
  have hur : (4 : ℝ) ≤ u := by exact_mod_cast hu
  have he : (2 : ℝ) ^ (1 - (u : ℝ)) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  norm_num at he
  exact ⟨hr.1, by linarith [hr.2]⟩

theorem sequence_active_gridAddress_ne_center
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (m : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0 < ell) (p : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z m k (u : ℝ) ((u : ℝ) + ell) p) :
    gridAddress (u + ell - 1)
      (sequencePoint Z m ((2 : ℝ) ^ k) x p) ≠ gridAddress (u + ell - 1) x := by
  have hlo := sequence_active_offset_lower Z s₀ s₁ x (u : ℝ) ((u : ℝ) + ell) m k p hp
  have hs := sequence_active_point_short Z s₀ s₁ x u ell m k hu p hp
  have hN : (0 : ℝ) < ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hlo hN
  rw [active_window_grid_scale u ell hell] at hscaled
  exact (gridAddress_ne_of_scaled_small_gap (u + ell - 1) x
    (sequencePoint Z m ((2 : ℝ) ^ k) x p) (by linarith) hs.2.le).symm

theorem sequence_offset_ratio_of_log_gap
    (Z : LogScale) (s₀ s₁ x : ℝ) (m m' : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁)
    (hgap : 3 ≤ p.1.1 * (Z.z m' - Z.z m)) :
    8 * (sequencePoint Z m' ((2 : ℝ) ^ k) x p - x) ≤
      sequencePoint Z m ((2 : ℝ) ^ k) x p - x := by
  have hr : (2 : ℝ) ^ (((k : ℝ) - p.1.1 * Z.z m') + 3) ≤
      (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_add (by norm_num)] at hr
  norm_num at hr
  have ht : (0 : ℝ) ≤ p.2.1 := by linarith [p.2.2.1]
  have hm := mul_le_mul_of_nonneg_left hr ht
  have ho₁ := sequence_shifted_offset Z m p.1.1 p.2.1 k
  have ho₂ := sequence_shifted_offset Z m' p.1.1 p.2.1 k
  have hm' : 8 * (p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m')) ≤
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) := by
    nlinarith [hm]
  calc
    8 * (sequencePoint Z m' ((2 : ℝ) ^ k) x p - x) =
        8 * (p.2.1 * (2 : ℝ) ^ k * (input Z m') ^ p.1.1) := by
          simp only [sequencePoint, powerPoint, add_sub_cancel_left]
    _ = 8 * (p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m')) := by rw [sequence_shifted_offset]
    _ ≤ p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * Z.z m) := hm'
    _ = p.2.1 * (2 : ℝ) ^ k * (input Z m) ^ p.1.1 := by rw [sequence_shifted_offset]
    _ = sequencePoint Z m ((2 : ℝ) ^ k) x p - x := by
      simp only [sequencePoint, powerPoint]
      ring

theorem sequence_gridAddress_ne_of_log_gap
    (Z : LogScale) (s₀ s₁ x : ℝ) (u ell : ℕ) (m m' : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0 < ell) (p : PowerParams s₀ s₁)
    (hgap : 3 ≤ p.1.1 * (Z.z m' - Z.z m))
    (hp : sequencePowerActivation Z m k (u : ℝ) ((u : ℝ) + ell) p)
    (hp' : sequencePowerActivation Z m' k (u : ℝ) ((u : ℝ) + ell) p) :
    gridAddress (u + ell - 1)
      (sequencePoint Z m ((2 : ℝ) ^ k) x p) ≠
      gridAddress (u + ell - 1)
        (sequencePoint Z m' ((2 : ℝ) ^ k) x p) := by
  have hl := sequence_offset_ratio_of_log_gap Z s₀ s₁ x m m' k p hgap
  have hs := sequence_active_point_short Z s₀ s₁ x u ell m k hu p hp
  have hs' := sequence_active_point_short Z s₀ s₁ x u ell m' k hu p hp'
  have hN : (0 : ℝ) < ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) := by positivity
  have hlo := sequence_active_offset_lower Z s₀ s₁ x (u : ℝ) ((u : ℝ) + ell) m' k p hp'
  have hsep : 7 * (2 : ℝ) ^ (-((u : ℝ) + ell)) <
      sequencePoint Z m ((2 : ℝ) ^ k) x p -
        sequencePoint Z m' ((2 : ℝ) ^ k) x p := by
    linarith [hl, hlo]
  have hm := mul_lt_mul_of_pos_left hsep hN
  have he : ((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) *
      (7 * (2 : ℝ) ^ (-((u : ℝ) + ell))) = 28 := by
    calc
      _ = 7 * (((2 ^ (u + ell - 1 + 3) : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((u : ℝ) + ell))) := by ring
      _ = 28 := by
        rw [active_window_grid_scale u ell hell]
        norm_num
  rw [he] at hm
  exact (gridAddress_ne_of_scaled_small_gap (u + ell - 1)
    (sequencePoint Z m' ((2 : ℝ) ^ k) x p)
    (sequencePoint Z m ((2 : ℝ) ^ k) x p) (by linarith) (by linarith)).symm

end ErdosSimilarityGrowingGaps
