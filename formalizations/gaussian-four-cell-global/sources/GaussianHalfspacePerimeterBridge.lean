import GaussianBVIsometry
import GaussianIntrinsicInnerPerimeter
import GaussianHalfspaceFlux

/-! In arbitrary Euclidean dimension the actual closed-ball erosion and
conventional BV perimeters agree for a coordinate halfspace. -/
open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem coordinate_halfspace_closedBall_erosion (a t : ℝ) (ht : 0 ≤ t) :
    {x : Space (d+1) | ∀ y,dist y x ≤ t → a < y 0} =
      {x : Space (d+1) | a+t < x 0} := by
  let e : Space (d+1) := EuclideanSpace.basisFun (Fin (d+1)) ℝ 0
  have he : ‖e‖ = 1 := by simp [e]
  ext x
  constructor
  · intro hx
    have hd : dist (x-t • e) x ≤ t := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,he,mul_one,
        Real.norm_eq_abs,abs_of_nonneg ht]
    have hh := hx (x-t • e) hd
    have hcoord : (x-t • e) 0 = x 0-t := by simp [e]
    rw [hcoord] at hh
    change a+t < x 0
    linarith
  · intro hx y hy
    have hn : |y 0-x 0| ≤ t := by
      have hh := (PiLp.norm_apply_le (y-x) 0).trans (show ‖y-x‖ ≤ t by simpa only [dist_eq_norm] using hy)
      simpa only [PiLp.sub_apply,Real.norm_eq_abs] using hh
    have hlo := (abs_le.mp hn).1
    change a+t < x 0 at hx
    linarith

lemma gaussian_coordinate_halfspace_mass (a : ℝ) :
    (gaussian (d+1)).real {x : Space (d+1) | a < x 0} = standardTail a := by
  have he : ‖EuclideanSpace.basisFun (Fin (d+1)) ℝ 0‖ = 1 := by simp
  have hm : MeasurePreserving (fun x : Space (d+1) => x 0)
      (gaussian (d+1)) (gaussianReal 0 1) := by
    refine ⟨by fun_prop,?_⟩
    simpa only [EuclideanSpace.basisFun_inner] using
      gaussian_unit_inner_law (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) he
  exact hm.measureReal_preimage measurableSet_Ioi.nullMeasurableSet

theorem gaussianInnerPerimeter_coordinate_halfspace (a : ℝ) :
    gaussianInnerPerimeter {x : Space (d+1) | a < x 0} = standardDensity a := by
  have hd : HasDerivAt (fun t : ℝ => standardTail (a+t)) (-standardDensity a) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => a+t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
    have houter : HasDerivAt standardTail (-standardDensity a) (a+(0 : ℝ)) := by
      simpa only [add_zero] using standardTail_hasDerivAt a
    convert houter.comp (0 : ℝ) (h := fun t : ℝ => a+t) hinner using 1
    · rfl
    · ring
  have he : ∀ t ∈ Ici (0 : ℝ),
      gaussianErosionMass {x : Space (d+1) | a < x 0} t = standardTail (a+t) := by
    intro t ht
    unfold gaussianErosionMass
    change (gaussian (d+1)).real {x : Space (d+1) | ∀ y,dist y x ≤ t → a < y 0} = _
    rw [coordinate_halfspace_closedBall_erosion a t ht,
      gaussian_coordinate_halfspace_mass]
  have hc := hd.hasDerivWithinAt.congr_of_mem he self_mem_Ici
  rw [gaussianInnerPerimeter,hc.derivWithin (uniqueDiffOn_Ici 0 0 self_mem_Ici),neg_neg]

theorem gaussian_coordinate_halfspace_perimeter_bridge (a : ℝ) :
    gaussianBVPerimeter {x : Space (d+1) | a < x 0} =
      ENNReal.ofReal (gaussianInnerPerimeter {x : Space (d+1) | a < x 0}) := by
  rw [gaussianBVPerimeter_coordinate_halfspace,gaussianInnerPerimeter_coordinate_halfspace]

end GaussianMeasureBridge
