import GaussianPartition
import Mathlib.Data.Fintype.Lattice

/-! Actual standard Gaussian affine hyperplanes are null. In particular finite
families of distinct linear scores have a unique winning label almost surely. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ}

theorem gaussian_hyperplane_null (w : Space d) (hw : w ≠ 0) (a : ℝ) :
    gaussian d {x | ⟪w, x⟫ = a} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ w
  have hv : (Var[L; gaussian d]).toNNReal ≠ 0 := by
    rw [gaussian, variance_dual_stdGaussian]
    have hnorm : 0 < ‖L‖ := by
      simpa only [L, innerSL_apply_norm] using norm_pos_iff.mpr hw
    have hpos : 0 < ‖L‖ ^ 2 := sq_pos_of_pos hnorm
    exact ne_of_gt (Real.toNNReal_pos.mpr hpos)
  haveI := nullSingletonClass_gaussianReal
    (μ := (gaussian d)[L]) hv
  have hz : (gaussianReal ((gaussian d)[L]) (Var[L; gaussian d]).toNNReal) {a} = 0 :=
    measure_singleton a
  rw [← IsGaussian.map_eq_gaussianReal L,
    Measure.map_apply L.continuous.measurable (measurableSet_singleton a)] at hz
  simpa only [L, Set.preimage, Set.mem_singleton_iff, innerSL_apply_apply] using hz

theorem ae_scores_pairwise_ne (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    ∀ᵐ x ∂gaussian d, ∀ i j, i ≠ j → ⟪v i, x⟫ - b i ≠ ⟪v j, x⟫ - b j := by
  refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
  by_cases hij : i = j
  · exact ae_of_all _ fun _ h => False.elim (h hij)
  · have hw : v i - v j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hv h))
    have hnull := gaussian_hyperplane_null (v i - v j) hw (b i - b j)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    intro _ heq
    apply hx
    rw [inner_sub_left]
    linarith

/-- Strict winning cells; ties are deliberately excluded from this definition. -/
def winningCell (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) : Set (Space d) :=
  {x | ∀ j, j ≠ i → ⟪v j, x⟫ - b j < ⟪v i, x⟫ - b i}

theorem measurableSet_winningCell (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k) :
    MeasurableSet (winningCell v b i) := by
  unfold winningCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (by fun_prop) (by fun_prop)

variable [NeZero k]

theorem ae_unique_winner (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) : ∀ᵐ x ∂gaussian d, ∃ i, x ∈ winningCell v b i := by
  filter_upwards [ae_scores_pairwise_ne v b hv] with x hx
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j : Fin k => ⟪v j, x⟫ - b j)
  refine ⟨i, fun j hji => ?_⟩
  exact lt_of_le_of_ne (hi j) (hx j i hji)

end GaussianMeasureBridge
