import GaussianRealStein
import GaussianCoordinateSplit
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Genuine coordinate Gaussian integration by parts in arbitrary dimension.
Compactness of each actual coordinate slice is proved from compact support
of the spatial test, and the Gaussian product law is the proved one. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma joinCoordinate_line (y : Space d) (t : ℝ) :
    joinCoordinate t y = t • joinCoordinate 1 (0 : Space d)+joinCoordinate 0 y := by
  ext i
  cases i using Fin.cases <;> simp

lemma joinCoordinate_line_contDiff (y : Space d) :
    ContDiff ℝ 1 (fun t : ℝ => joinCoordinate t y) := by
  have he : (fun t : ℝ => joinCoordinate t y) =
      (fun t : ℝ => t • joinCoordinate 1 (0 : Space d)+joinCoordinate 0 y) :=
    funext (joinCoordinate_line y)
  rw [he]
  fun_prop

lemma joinCoordinate_line_hasDerivAt (y : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => joinCoordinate s y) (joinCoordinate 1 (0 : Space d)) t := by
  convert ((hasDerivAt_id t).smul_const (joinCoordinate 1 (0 : Space d))).add_const
    (joinCoordinate 0 y) using 1
  · exact funext (joinCoordinate_line y)
  · simp

lemma compact_coordinate_slice (f : Space (d+1) → ℝ) (hs : HasCompactSupport f) (y : Space d) :
    HasCompactSupport (fun t : ℝ => f (joinCoordinate t y)) := by
  have hc : IsCompact ((fun x : Space (d+1) => x 0) '' tsupport f) := hs.image (by fun_prop)
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro t ht
  exact ⟨joinCoordinate t y,subset_tsupport f ht,rfl⟩

noncomputable def firstCoordinateStein (f : Space (d+1) → ℝ) (x : Space (d+1)) : ℝ :=
  fderiv ℝ f x (joinCoordinate 1 (0 : Space d))-x 0*f x

lemma firstCoordinateStein_continuous (f : Space (d+1) → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (firstCoordinateStein f) := by
  have hc := hf.continuous
  have hd := hf.continuous_fderiv one_ne_zero
  unfold firstCoordinateStein
  fun_prop

lemma firstCoordinateStein_compact (f : Space (d+1) → ℝ) (hs : HasCompactSupport f) :
    HasCompactSupport (firstCoordinateStein f) := by
  apply hs.mono'
  intro x hx
  by_contra he
  have hz : f x = 0 := Function.notMem_support.mp (fun h => he (subset_tsupport _ h))
  apply hx
  simp [firstCoordinateStein,fderiv_of_notMem_tsupport ℝ he,hz]

theorem gaussian_first_coordinate_stein
    (f : Space (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    (∫ x,firstCoordinateStein f x ∂gaussian (d+1)) = 0 := by
  have hi : Integrable (firstCoordinateStein f) (gaussian (d+1)) :=
    (firstCoordinateStein_continuous f hf).integrable_of_hasCompactSupport (firstCoordinateStein_compact f hs)
  have hm := gaussian_joinCoordinate_swapped_preserving (d := d)
  have hip : Integrable (fun z : Space d × ℝ => firstCoordinateStein f (joinCoordinate z.2 z.1))
      ((gaussian d).prod (gaussianReal 0 1)) := hm.integrable_comp_of_integrable hi
  have he : (∫ x,firstCoordinateStein f x ∂gaussian (d+1)) =
      ∫ z : Space d × ℝ,firstCoordinateStein f (joinCoordinate z.2 z.1)
        ∂(gaussian d).prod (gaussianReal 0 1) := by
    rw [← hm.map_eq,integral_map hm.measurable.aemeasurable
      (firstCoordinateStein_continuous f hf).aestronglyMeasurable]
  rw [he,integral_prod _ hip]
  have hy (y : Space d) : (∫ t,firstCoordinateStein f (joinCoordinate t y) ∂gaussianReal 0 1) = 0 := by
    have hslice := hf.comp (joinCoordinate_line_contDiff y)
    have hd (t : ℝ) : deriv (fun s : ℝ => f (joinCoordinate s y)) t =
        fderiv ℝ f (joinCoordinate t y) (joinCoordinate 1 (0 : Space d)) :=
      ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
        (joinCoordinate_line_hasDerivAt y t)).deriv
    have hz := gaussianReal_stein_integral_zero _ hslice (compact_coordinate_slice f hs y)
    convert hz using 1
    congr 1
    funext t
    simp only [firstCoordinateStein,joinCoordinate_zero,Function.comp_def,hd]
  simp only [hy,integral_zero]

end GaussianMeasureBridge
