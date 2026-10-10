import GaussianFour.ScalarTent
import GaussianWinningPartition
import Mathlib.Tactic.FieldSimp

/-!
Uniform separation of actual Gaussian first moments for halfspace-separated
fractional labels. The final winning-cell specialization is the analytic
pair-separation lemma needed at the singular covariance boundary.
-/

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge

namespace GaussianFour

variable {d k : ℕ}

lemma unit_projection_gaussian_law (n : Space d) (hn : ‖n‖ = 1) :
    (gaussian d).map (fun x => ⟪n,x⟫) = gaussianReal 0 1 := by
  have h := IsGaussian.map_eq_gaussianReal (μ := gaussian d) (innerSL ℝ n)
  simpa only [gaussian, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hn, one_pow, Real.toNNReal_one, innerSL_apply_apply] using h

lemma integrable_projection_tent (n : Space d) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    Integrable (fun x => tent r t ⟪n,x⟫) (gaussian d) := by
  apply (integrable_const r).mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _ _)]
    exact tent_le_radius hr _ _

/-- The one-dimensional Gaussian cap estimate transported through the actual
standard Gaussian linear-functional law, without a Gaussian-law assumption. -/
theorem integral_projection_tent_le (n : Space d) (hn : ‖n‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    (∫ x, tent r t ⟪n,x⟫ ∂gaussian d) ≤ densityBound * r^2 := by
  have hmap := integral_map (μ := gaussian d)
    (φ := fun x : Space d => ⟪n,x⟫)
    (by fun_prop) (continuous_tent r t).aestronglyMeasurable
  rw [unit_projection_gaussian_law n hn] at hmap
  rw [← hmap]
  exact gaussian_integral_tent_le hr t

lemma separated_label_tent_bound {a b z t r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a+b ≤ 1)
    (ha_side : 0 < a → t ≤ z) (hb_side : 0 < b → z ≤ t) :
    r*(a+b) - tent r t z ≤ a*(z-t) - b*(z-t) := by
  have hza : |z-t|*a = (z-t)*a := by
    by_cases he : a=0
    · simp [he]
    · rw [abs_of_nonneg (sub_nonneg.mpr (ha_side (lt_of_le_of_ne ha (Ne.symm he))))]
  have hzb : |z-t|*b = -(z-t)*b := by
    by_cases he : b=0
    · simp [he]
    · rw [abs_of_nonpos (sub_nonpos.mpr (hb_side (lt_of_le_of_ne hb (Ne.symm he))))]
  have h1 := mul_le_mul_of_nonneg_right (le_max_left (r-|z-t|) 0) (add_nonneg ha hb)
  have h2 := mul_le_mul_of_nonneg_left hs (tent_nonneg r t z)
  change (r-|z-t|)*(a+b) ≤ tent r t z*(a+b) at h1
  nlinarith

lemma fractional_pair_sum_le_one (F : FractionalPartition d k)
    (i j : Fin k) (hij : i ≠ j) :
    ∀ᵐ x ∂gaussian d, F.labels i x + F.labels j x ≤ 1 := by
  classical
  have hn : ∀ᵐ x ∂gaussian d, ∀ l, 0 ≤ F.labels l x := ae_all_iff.mpr F.nonneg
  filter_upwards [hn,F.sum_one] with x hx hsum
  have hle : (∑ l ∈ ({i,j} : Finset (Fin k)), F.labels l x) ≤
      ∑ l : Fin k, F.labels l x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro l _ _
    exact hx l
  simpa only [Finset.sum_pair hij, hsum] using hle

variable [NeZero k]

/-- A quadratic lower bound for the projected difference of two actual Bochner
moments, from their masses and their separation by a unit-normal hyperplane. -/
theorem separated_moments_quadratic (F : FractionalPartition d k)
    (i j : Fin k) (hij : i ≠ j) (n : Space d) (hn : ‖n‖ = 1)
    (p t r : ℝ) (hr : 0 ≤ r) (hi : F.mass i=p) (hj : F.mass j=p)
    (hside_i : ∀ᵐ x ∂gaussian d, 0 < F.labels i x → t ≤ ⟪n,x⟫)
    (hside_j : ∀ᵐ x ∂gaussian d, 0 < F.labels j x → ⟪n,x⟫ ≤ t) :
    2*p*r - densityBound*r^2 ≤ ⟪n,F.moment i-F.moment j⟫ := by
  have hpw : ∀ᵐ x ∂gaussian d,
      r*(F.labels i x+F.labels j x) - tent r t ⟪n,x⟫ ≤
        F.labels i x*(⟪n,x⟫-t) - F.labels j x*(⟪n,x⟫-t) := by
    filter_upwards [F.nonneg i,F.nonneg j,fractional_pair_sum_le_one F i j hij,
      hside_i,hside_j] with x ha hb hs hsi hsj
    exact separated_label_tent_bound ha hb hs hsi hsj
  have hl := ((F.integrable_label i).add (F.integrable_label j)).const_mul r
  have ht := integrable_projection_tent n hr t
  have hri := F.integrable_weighted_score i n t
  have hrj := F.integrable_weighted_score j n t
  have hle := integral_mono_ae (hl.sub ht) (hri.sub hrj) hpw
  rw [integral_sub hl ht, integral_const_mul,
    integral_add (F.integrable_label i) (F.integrable_label j),
    integral_sub hri hrj, F.integral_weighted_score, F.integral_weighted_score] at hle
  change r*(F.mass i+F.mass j) - (∫ x, tent r t ⟪n,x⟫ ∂gaussian d) ≤
    (⟪n,F.moment i⟫-F.mass i*t) - (⟪n,F.moment j⟫-F.mass j*t) at hle
  rw [hi,hj] at hle
  have htbound := integral_projection_tent_le n hn hr t
  rw [inner_sub_right]
  nlinarith

/-- Exact uniform pair separation. No isoperimetric or multi-bubble input is
used: the constant is obtained by optimizing the Gaussian cap estimate. -/
theorem separated_moments (F : FractionalPartition d k)
    (i j : Fin k) (hij : i ≠ j) (n : Space d) (hn : ‖n‖ = 1)
    (p t : ℝ) (hi : F.mass i=p) (hj : F.mass j=p)
    (hside_i : ∀ᵐ x ∂gaussian d, 0 < F.labels i x → t ≤ ⟪n,x⟫)
    (hside_j : ∀ᵐ x ∂gaussian d, 0 < F.labels j x → ⟪n,x⟫ ≤ t) :
    p^2/densityBound ≤ ⟪n,F.moment i-F.moment j⟫ := by
  have hp : 0 ≤ p := hi ▸ F.mass_nonneg i
  have h := separated_moments_quadratic F i j hij n hn p t
    (p/densityBound) (div_nonneg hp densityBound_pos.le) hi hj hside_i hside_j
  have he : 2*p*(p/densityBound)-densityBound*(p/densityBound)^2 = p^2/densityBound := by
    field_simp [ne_of_gt densityBound_pos]
    <;> ring
  rwa [he] at h

end GaussianFour
