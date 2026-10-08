import GaussianDivergenceStein

/-! Exact smooth-test Gaussian divergence flux through a coordinate
halfspace in every dimension. The non-normal coordinate terms vanish by
actual Fubini integration, including all compact-support obligations. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

@[simp] lemma joinAt_zero (t : ℝ) (y : Space d) :
    joinAt 0 t y = joinCoordinate t y := by
  ext j
  simp [joinAt,joinCoordinate,Fin.insertNth_zero']

lemma coordinate_stein_slice_integral_zero (i : Fin (d+1))
    (f : Space (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (y : Space d) :
    (∫ t,coordinateStein i f (joinAt i t y) ∂gaussianReal 0 1) = 0 := by
  have hslice := hf.comp (joinAt_line_contDiff i y)
  have hd (t : ℝ) : deriv (fun s : ℝ => f (joinAt i s y)) t =
      fderiv ℝ f (joinAt i t y) (EuclideanSpace.basisFun (Fin (d+1)) ℝ i) :=
    ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
      (joinAt_line_hasDerivAt i y t)).deriv
  have hz := gaussianReal_stein_integral_zero _ hslice (compact_slice_at i f hs y)
  convert hz using 1
  congr 1
  funext t
  simp only [coordinateStein,joinAt_same,Function.comp_def,hd]

theorem gaussian_coordinate_halfspace_flux (i : Fin (d+1)) (a : ℝ)
    (f : Space (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    (∫ x in {x : Space (d+1) | a < x 0},coordinateStein i f x ∂gaussian (d+1)) =
      if i=0 then -standardDensity a*(∫ y,f (joinCoordinate a y) ∂gaussian d) else 0 := by
  let H : Set (Space (d+1)) := {x | a < x 0}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (by fun_prop)
  have hc := coordinateStein_continuous i f hf
  have hi : Integrable (coordinateStein i f) (gaussian (d+1)) :=
    hc.integrable_of_hasCompactSupport (coordinateStein_compact i f hs)
  have hm := gaussian_joinAt_swapped_preserving i
  have hip : Integrable (fun z : Space d × ℝ =>
      H.indicator (coordinateStein i f) (joinAt i z.2 z.1))
      ((gaussian d).prod (gaussianReal 0 1)) :=
    hm.integrable_comp_of_integrable (hi.indicator hH)
  have he : (∫ x in H,coordinateStein i f x ∂gaussian (d+1)) =
      ∫ z : Space d × ℝ,H.indicator (coordinateStein i f) (joinAt i z.2 z.1)
        ∂(gaussian d).prod (gaussianReal 0 1) := by
    rw [← integral_indicator hH,← hm.map_eq,integral_map hm.measurable.aemeasurable
      (hc.measurable.indicator hH).aestronglyMeasurable]
  change (∫ x in H,coordinateStein i f x ∂gaussian (d+1)) = _
  rw [he,integral_prod _ hip]
  by_cases hi0 : i=0
  · subst i
    simp only [ite_true]
    have hy (y : Space d) :
        (∫ t,H.indicator (coordinateStein 0 f) (joinAt 0 t y) ∂gaussianReal 0 1) =
          -standardDensity a*f (joinCoordinate a y) := by
      have hslice := hf.comp (joinCoordinate_line_contDiff y)
      have hd (t : ℝ) : deriv (fun s : ℝ => f (joinCoordinate s y)) t =
          fderiv ℝ f (joinCoordinate t y) (EuclideanSpace.basisFun (Fin (d+1)) ℝ 0) := by
        rw [← joinAt_one 0,joinAt_zero]
        exact ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
          (joinCoordinate_line_hasDerivAt y t)).deriv
      have hfunc : (fun t => H.indicator (coordinateStein 0 f) (joinAt 0 t y)) =
          (Ioi a).indicator (fun t => deriv (fun s => f (joinCoordinate s y)) t-t*f (joinCoordinate t y)) := by
        funext t
        simp only [joinAt_zero,Set.indicator_apply,H,mem_ofPred_eq,joinCoordinate_zero,
          coordinateStein,mem_Ioi,hd]
        rfl
      rw [hfunc,integral_indicator measurableSet_Ioi]
      exact gaussianReal_halfline_weighted_flux _ hslice (compact_coordinate_slice f hs y) a
    simp_rw [hy]
    exact integral_const_mul _ _
  · simp only [hi0,ite_false]
    obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq (x := (0 : Fin (d+1))) (y := i) (Ne.symm hi0)
    have hy (y : Space d) :
        (∫ t,H.indicator (coordinateStein i f) (joinAt i t y) ∂gaussianReal 0 1) = 0 := by
      have hj0 (t : ℝ) : joinAt i t y 0 = y j := by rw [← hj,joinAt_succAbove]
      by_cases hay : a < y j
      · have hfunc : (fun t => H.indicator (coordinateStein i f) (joinAt i t y)) =
            (fun t => coordinateStein i f (joinAt i t y)) := by
          funext t
          simp [H,hj0,hay]
        rw [hfunc]
        exact coordinate_stein_slice_integral_zero i f hf hs y
      · have hfunc : (fun t => H.indicator (coordinateStein i f) (joinAt i t y)) = 0 := by
          funext t
          simp [H,hj0,hay]
        rw [hfunc]
        simp
    simp only [hy,integral_zero]

theorem gaussian_halfspace_test_divergence (a : ℝ) (X : GaussianTestField (d+1)) :
    (∫ x in {x : Space (d+1) | a < x 0},gaussianDivergence X x ∂gaussian (d+1)) =
      -standardDensity a*(∫ y,(X (joinCoordinate a y)) 0 ∂gaussian d) := by
  have hc : ContDiff ℝ 1 X := X.smooth.of_le (by simp)
  have hi (i : Fin (d+1)) : IntegrableOn (coordinateStein i (fun z => X z i))
      {x : Space (d+1) | a < x 0} (gaussian (d+1)) :=
    ((coordinateStein_continuous i _ (coordinate_of_field_contDiff X hc i)).integrable_of_hasCompactSupport
      (coordinateStein_compact i _ (coordinate_of_field_compact X X.compact i))).integrableOn
  simp_rw [gaussianDivergence_coordinate_sum X (hc.differentiable one_ne_zero)]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [gaussian_coordinate_halfspace_flux _ a _ (coordinate_of_field_contDiff X hc _)
    (coordinate_of_field_compact X X.compact _)]
  simp

end GaussianMeasureBridge
