import GaussianPartition
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Full support of the actual finite-dimensional standard Gaussian.
It is proved from its product-real-Gaussian realization, not assumed. -/

open MeasureTheory ProbabilityTheory
open WithLp
open scoped NNReal

namespace GaussianMeasureBridge

instance realGaussian_openPos : (gaussianReal 0 1).IsOpenPosMeasure := by
  exact (gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure

instance gaussian_openPos (d : ℕ) : (gaussian d).IsOpenPosMeasure := by
  unfold gaussian
  rw [← map_pi_eq_stdGaussian]
  exact (by fun_prop : Continuous (toLp 2 : (Fin d → ℝ) → Space d)).isOpenPosMeasure_map
    (toLp_surjective 2)

theorem gaussian_open_pos {d : ℕ} (U : Set (Space d))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < gaussian d U :=
  hU.measure_pos (gaussian d) hne

end GaussianMeasureBridge
