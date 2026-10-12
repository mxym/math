import GaussianRealBVPerimeter
import GaussianTailCalculus

/-! The actual distance-erosion and variational perimeters agree for every
Gaussian half-line. This is the base case of the conventional BV bridge. -/
open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ENNReal
namespace GaussianMeasureBridge

noncomputable def gaussianRealErosionMass (S : Set ℝ) (t : ℝ) : ℝ :=
  (gaussianReal 0 1).real {x | ∀ y : ℝ,dist y x ≤ t → y ∈ S}

noncomputable def gaussianRealInnerPerimeter (S : Set ℝ) : ℝ :=
  -derivWithin (gaussianRealErosionMass S) (Ici 0) 0

theorem halfline_closedBall_erosion (a t : ℝ) (ht : 0 ≤ t) :
    {x : ℝ | ∀ y : ℝ,dist y x ≤ t → y ∈ Ioi a} = Ioi (a+t) := by
  ext x
  constructor
  · intro hx
    have hh := hx (x-t) (by simp [Real.dist_eq,abs_of_nonneg ht])
    change a < x-t at hh
    change a+t < x
    linarith
  · intro hx y hy
    have hh := (abs_le.mp (show |y-x| ≤ t by simpa only [Real.dist_eq] using hy)).1
    change a+t < x at hx
    change a < y
    linarith

theorem gaussianRealInnerPerimeter_halfline (a : ℝ) :
    gaussianRealInnerPerimeter (Ioi a) = standardDensity a := by
  have hd : HasDerivAt (fun t : ℝ => standardTail (a+t)) (-standardDensity a) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => a+t) 1 0 := (hasDerivAt_id (0:ℝ)).const_add a
    have houter : HasDerivAt standardTail (-standardDensity a) (a+(0:ℝ)) := by
      simpa only [add_zero] using standardTail_hasDerivAt a
    have he := houter.comp (0:ℝ) (h := fun t : ℝ => a+t) hinner
    convert he using 1
    · rfl
    · ring
  have he : ∀ t ∈ Ici (0:ℝ),gaussianRealErosionMass (Ioi a) t = standardTail (a+t) := by
    intro t ht
    rw [gaussianRealErosionMass,halfline_closedBall_erosion a t ht]
    rfl
  have hc := hd.hasDerivWithinAt.congr_of_mem he self_mem_Ici
  rw [gaussianRealInnerPerimeter,hc.derivWithin (uniqueDiffOn_Ici 0 0 self_mem_Ici),neg_neg]

theorem gaussianReal_halfline_perimeter_bridge (a : ℝ) :
    gaussianRealBVPerimeter (Ioi a) = ENNReal.ofReal (gaussianRealInnerPerimeter (Ioi a)) := by
  rw [gaussianRealBVPerimeter_halfline,gaussianRealInnerPerimeter_halfline]

end GaussianMeasureBridge
