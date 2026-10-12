import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Actual finite-dimensional standard Gaussian fractional partitions.
There are no abstract Gaussian-property hypotheses: every integral is taken
against Mathlib's `ProbabilityTheory.stdGaussian` on the stated Euclidean space.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)

instance (d : ℕ) : IsProbabilityMeasure (gaussian d) := by
  unfold gaussian
  infer_instance

instance (d : ℕ) : IsGaussian (gaussian d) := by
  unfold gaussian
  infer_instance

/-- A finite measurable fractional partition, with simplex constraints a.e. -/
structure FractionalPartition (d k : ℕ) where
  labels : Fin k → Space d → ℝ
  measurable_labels : ∀ i, Measurable (labels i)
  nonneg : ∀ i, ∀ᵐ x ∂gaussian d, 0 ≤ labels i x
  le_one : ∀ i, ∀ᵐ x ∂gaussian d, labels i x ≤ 1
  sum_one : ∀ᵐ x ∂gaussian d, ∑ i, labels i x = 1

namespace FractionalPartition

variable {d k : ℕ} (F : FractionalPartition d k)

noncomputable def mass (i : Fin k) : ℝ := ∫ x, F.labels i x ∂gaussian d

noncomputable def moment (i : Fin k) : Space d :=
  ∫ x, F.labels i x • x ∂gaussian d

lemma norm_label_le_one (i : Fin k) : ∀ᵐ x ∂gaussian d, ‖F.labels i x‖ ≤ 1 := by
  filter_upwards [F.nonneg i, F.le_one i] with x hx hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hy

theorem integrable_label (i : Fin k) : Integrable (F.labels i) (gaussian d) := by
  exact (integrable_const (1 : ℝ)).mono'
    (F.measurable_labels i).aestronglyMeasurable (F.norm_label_le_one i)

/-- The actual vector-valued Bochner first-moment integrand is integrable. -/
theorem integrable_weighted_id (i : Fin k) :
    Integrable (fun x => F.labels i x • x) (gaussian d) := by
  exact (IsGaussian.integrable_id (μ := gaussian d)).bdd_smul 1
    (F.measurable_labels i).aestronglyMeasurable (F.norm_label_le_one i)

theorem mass_nonneg (i : Fin k) : 0 ≤ F.mass i := by
  exact integral_nonneg_of_ae (F.nonneg i)

theorem sum_mass : ∑ i, F.mass i = 1 := by
  simp only [mass]
  rw [← integral_finsetSum Finset.univ (fun i _ => F.integrable_label i)]
  calc
    (∫ x, ∑ i, F.labels i x ∂gaussian d) = ∫ _, (1 : ℝ) ∂gaussian d :=
      integral_congr_ae F.sum_one
    _ = 1 := by simp

/-- First moments sum to the actual Gaussian mean, which is zero. -/
theorem sum_moment : ∑ i, F.moment i = 0 := by
  simp only [moment]
  rw [← integral_finsetSum Finset.univ (fun i _ => F.integrable_weighted_id i)]
  have h : (fun x => ∑ i, F.labels i x • x) =ᵐ[gaussian d] fun x => x := by
    filter_upwards [F.sum_one] with x hx
    rw [← Finset.sum_smul, hx, one_smul]
  rw [integral_congr_ae h]
  exact integral_id_stdGaussian

theorem inner_moment (i : Fin k) (v : Space d) :
    ⟪v, F.moment i⟫ = ∫ x, F.labels i x * ⟪v, x⟫ ∂gaussian d := by
  simpa only [moment, innerSL_apply_apply, real_inner_smul_right]
    using ((innerSL ℝ v).integral_comp_comm (F.integrable_weighted_id i)).symm

end FractionalPartition

variable {d k : ℕ} [NeZero k]

/-- The ordinary finite score maximum; no essential supremum abstraction. -/
noncomputable def scoreMax (v : Fin k → Space d) (b : Fin k → ℝ) (x : Space d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫ - b i)

lemma le_scoreMax (v : Fin k → Space d) (b : Fin k → ℝ) (x : Space d) (i : Fin k) :
    ⟪v i, x⟫ - b i ≤ scoreMax v b x := by
  unfold scoreMax
  exact Finset.le_sup' (fun j : Fin k => ⟪v j, x⟫ - b j) (Finset.mem_univ i)

theorem integrable_score (v : Space d) (b : ℝ) :
    Integrable (fun x => ⟪v, x⟫ - b) (gaussian d) := by
  exact ((innerSL ℝ v).integrable_comp (IsGaussian.integrable_id (μ := gaussian d))).sub
    (integrable_const b)

theorem integrable_scoreMax (v : Fin k → Space d) (b : Fin k → ℝ) :
    Integrable (scoreMax v b) (gaussian d) := by
  have h : Integrable (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin k => fun x : Space d => ⟪v i, x⟫ - b i)) (gaussian d) := by
    exact Finset.sup'_induction
      (p := fun g : Space d → ℝ => Integrable g (gaussian d))
      Finset.univ_nonempty (fun i : Fin k => fun x : Space d => ⟪v i, x⟫ - b i)
      (fun f hf g hg => hf.sup hg) (fun i _ => integrable_score (v i) (b i))
  have heq : (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin k => fun x : Space d => ⟪v i, x⟫ - b i)) = scoreMax v b := by
    funext x
    exact Finset.sup'_apply _ _ _
  rwa [heq] at h

theorem continuous_scoreMax (v : Fin k → Space d) (b : Fin k → ℝ) :
    Continuous (scoreMax v b) := by
  exact Continuous.finset_sup'_apply _ (fun i _ => by fun_prop)

namespace FractionalPartition

variable (F : FractionalPartition d k)

lemma integrable_weighted_score (i : Fin k) (v : Space d) (b : ℝ) :
    Integrable (fun x => F.labels i x * (⟪v, x⟫ - b)) (gaussian d) := by
  exact (integrable_score v b).bdd_mul (F.measurable_labels i).aestronglyMeasurable
    (F.norm_label_le_one i)

lemma integral_weighted_score (i : Fin k) (v : Space d) (b : ℝ) :
    (∫ x, F.labels i x * (⟪v, x⟫ - b) ∂gaussian d) =
      ⟪v, F.moment i⟫ - F.mass i * b := by
  simp_rw [mul_sub]
  rw [integral_sub]
  · rw [← F.inner_moment i v, integral_mul_const]
    rfl
  · exact (integrable_score v 0).bdd_mul
      (F.measurable_labels i).aestronglyMeasurable (F.norm_label_le_one i) |>.congr
      (ae_of_all _ fun x => by simp)
  · exact (F.integrable_label i).mul_const b

/-- Actual Gaussian price-dual domination for arbitrary scores and prices. -/
theorem price_dual (v : Fin k → Space d) (b : Fin k → ℝ) :
    (∑ i, ⟪v i, F.moment i⟫) ≤
      (∫ x, scoreMax v b x ∂gaussian d) + ∑ i, F.mass i * b i := by
  have hp : ∀ᵐ x ∂gaussian d,
      ∑ i, F.labels i x * (⟪v i, x⟫ - b i) ≤ scoreMax v b x := by
    have hn : ∀ᵐ x ∂gaussian d, ∀ i, 0 ≤ F.labels i x :=
      ae_all_iff.mpr F.nonneg
    filter_upwards [hn, F.sum_one] with x hx hsum
    calc
      (∑ i, F.labels i x * (⟪v i, x⟫ - b i)) ≤
          ∑ i, F.labels i x * scoreMax v b x :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (le_scoreMax v b x i) (hx i)
      _ = (∑ i, F.labels i x) * scoreMax v b x :=
        (Finset.sum_mul ..).symm
      _ = scoreMax v b x := by rw [hsum, one_mul]
  have hi := integral_mono_ae
    (integrable_finsetSum _ (fun i _ => F.integrable_weighted_score i (v i) (b i)))
    (integrable_scoreMax v b) hp
  rw [integral_finsetSum Finset.univ
    (fun i _ => F.integrable_weighted_score i (v i) (b i))] at hi
  simp_rw [F.integral_weighted_score] at hi
  rw [Finset.sum_sub_distrib] at hi
  linarith

end FractionalPartition
end GaussianMeasureBridge
