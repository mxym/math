import GaussianHalfspacePerimeterBridge

/-! Exact agreement of actual distance-erosion and conventional variational
perimeters for any unit-normal halfspace, at every offset and in arbitrary
positive dimension. The orthogonal transformation is an explicit reflection. -/
open MeasureTheory ProbabilityTheory Set Metric Filter Module
open scoped Topology ENNReal RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem unit_halfspace_closedBall_erosion (u : Space (d+1)) (hu : ‖u‖=1)
    (a t : ℝ) (ht : 0 ≤ t) :
    {x | ∀ y : Space (d+1),dist y x ≤ t → a < ⟪u,y⟫} =
      {x | a+t < ⟪u,x⟫} := by
  ext x
  constructor
  · intro hx
    have hd : dist (x-t • u) x ≤ t := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,hu,mul_one,
        Real.norm_eq_abs,abs_of_nonneg ht]
    have hh := hx (x-t • u) hd
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hu] at hh
    change a+t < ⟪u,x⟫
    nlinarith
  · intro hx y hy
    have hn : ‖x-y‖ ≤ t := by simpa only [dist_eq_norm,norm_sub_rev] using hy
    have hb := (real_inner_le_norm u (x-y)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg u))
    rw [inner_sub_right,hu,one_mul] at hb
    change a+t < ⟪u,x⟫ at hx
    linarith

lemma gaussian_unit_halfspace_mass (u : Space (d+1)) (hu : ‖u‖=1) (a : ℝ) :
    (gaussian (d+1)).real {x | a < ⟪u,x⟫} = standardTail a := by
  have hm : MeasurePreserving (fun x : Space (d+1) => ⟪u,x⟫)
      (gaussian (d+1)) (gaussianReal 0 1) :=
    ⟨by fun_prop,gaussian_unit_inner_law u hu⟩
  exact hm.measureReal_preimage measurableSet_Ioi.nullMeasurableSet

theorem gaussianInnerPerimeter_unit_halfspace (u : Space (d+1)) (hu : ‖u‖=1) (a : ℝ) :
    gaussianInnerPerimeter {x | a < ⟪u,x⟫} = standardDensity a := by
  have hd : HasDerivAt (fun t : ℝ => standardTail (a+t)) (-standardDensity a) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => a+t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
    have houter : HasDerivAt standardTail (-standardDensity a) (a+(0 : ℝ)) := by
      simpa only [add_zero] using standardTail_hasDerivAt a
    convert houter.comp (0 : ℝ) (h := fun t : ℝ => a+t) hinner using 1
    · rfl
    · ring
  have he : ∀ t ∈ Ici (0 : ℝ),gaussianErosionMass {x | a < ⟪u,x⟫} t = standardTail (a+t) := by
    intro t ht
    unfold gaussianErosionMass
    change (gaussian (d+1)).real {x | ∀ y,dist y x ≤ t → a < ⟪u,y⟫} = _
    rw [unit_halfspace_closedBall_erosion u hu a t ht,
      gaussian_unit_halfspace_mass u hu]
  have hc := hd.hasDerivWithinAt.congr_of_mem he self_mem_Ici
  rw [gaussianInnerPerimeter,hc.derivWithin (uniqueDiffOn_Ici 0 0 self_mem_Ici),neg_neg]

theorem gaussianBVPerimeter_unit_halfspace (u : Space (d+1)) (hu : ‖u‖=1) (a : ℝ) :
    gaussianBVPerimeter {x | a < ⟪u,x⟫} = ENNReal.ofReal (standardDensity a) := by
  let e : Space (d+1) := EuclideanSpace.basisFun (Fin (d+1)) ℝ 0
  have he : ‖e‖=1 := by simp [e]
  let T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1) := (ℝ ∙ (u-e))ᗮ.reflection
  have hT : T u=e := Submodule.reflection_sub (hu.trans he.symm)
  have hi (x : Space (d+1)) : (T x) 0=⟪u,x⟫ := by
    rw [← EuclideanSpace.basisFun_inner]
    change ⟪e,T x⟫=⟪u,x⟫
    rw [← hT,T.inner_map_map]
  have hS : {x | a < ⟪u,x⟫} = T ⁻¹' {x : Space (d+1) | a < x 0} := by
    ext x
    simp only [mem_preimage,mem_ofPred_eq,hi]
  rw [hS,gaussianBVPerimeter_isometry T _ (measurableSet_lt measurable_const (by fun_prop)),
    gaussianBVPerimeter_coordinate_halfspace]

theorem gaussian_unit_halfspace_perimeter_bridge (u : Space (d+1)) (hu : ‖u‖=1) (a : ℝ) :
    gaussianBVPerimeter {x | a < ⟪u,x⟫} = ENNReal.ofReal (gaussianInnerPerimeter {x | a < ⟪u,x⟫}) := by
  rw [gaussianBVPerimeter_unit_halfspace u hu,gaussianInnerPerimeter_unit_halfspace u hu]

end GaussianMeasureBridge
