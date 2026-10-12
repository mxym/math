import GaussianCoordinateStein

/-! Gaussian integration by parts for every actual coordinate. The product
law is proved at the requested coordinate, rather than assumed by symmetry. -/
open MeasureTheory ProbabilityTheory Module Set
open scoped Topology RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def joinAt (i : Fin (d+1)) (t : ℝ) (y : Space d) : Space (d+1) :=
  WithLp.toLp 2 (Fin.insertNth i t (fun j => y j))

@[simp] lemma joinAt_same (i : Fin (d+1)) (t : ℝ) (y : Space d) :
    joinAt i t y i = t := by simp [joinAt]

@[simp] lemma joinAt_succAbove (i : Fin (d+1)) (t : ℝ) (y : Space d) (j : Fin d) :
    joinAt i t y (i.succAbove j) = y j := by simp [joinAt]

lemma gaussian_joinAt_preserving (i : Fin (d+1)) :
    MeasurePreserving (fun z : ℝ × Space d => joinAt i z.1 z.2)
      ((gaussianReal 0 1).prod (gaussian d)) (gaussian (d+1)) := by
  have hp := (MeasurePreserving.id (gaussianReal 0 1)).prod (gaussian_ofLp_preserving d)
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => gaussianReal 0 1) i).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i)
  have hh := (gaussian_toLp_preserving (d+1)).comp (he.comp hp)
  convert hh using 1
  funext z
  ext j
  simp [joinAt,Function.comp_def,MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]

lemma gaussian_joinAt_swapped_preserving (i : Fin (d+1)) :
    MeasurePreserving (fun z : Space d × ℝ => joinAt i z.2 z.1)
      ((gaussian d).prod (gaussianReal 0 1)) (gaussian (d+1)) :=
  (gaussian_joinAt_preserving i).comp Measure.measurePreserving_swap

lemma joinAt_one (i : Fin (d+1)) :
    joinAt i 1 (0 : Space d) = EuclideanSpace.basisFun (Fin (d+1)) ℝ i := by
  ext j
  induction j using i.succAboveCases
  · simp [EuclideanSpace.basisFun_apply]
  · simp [EuclideanSpace.basisFun_apply,Fin.succAbove_ne]

lemma joinAt_line (i : Fin (d+1)) (y : Space d) (t : ℝ) :
    joinAt i t y = t • EuclideanSpace.basisFun (Fin (d+1)) ℝ i + joinAt i 0 y := by
  rw [← joinAt_one i]
  ext j
  induction j using i.succAboveCases <;> simp

lemma joinAt_line_contDiff (i : Fin (d+1)) (y : Space d) :
    ContDiff ℝ 1 (fun t : ℝ => joinAt i t y) := by
  have he : (fun t : ℝ => joinAt i t y) =
      (fun t : ℝ => t • EuclideanSpace.basisFun (Fin (d+1)) ℝ i + joinAt i 0 y) :=
    funext (joinAt_line i y)
  rw [he]
  fun_prop

lemma joinAt_line_hasDerivAt (i : Fin (d+1)) (y : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => joinAt i s y)
      (EuclideanSpace.basisFun (Fin (d+1)) ℝ i) t := by
  convert ((hasDerivAt_id t).smul_const (EuclideanSpace.basisFun (Fin (d+1)) ℝ i)).add_const
    (joinAt i 0 y) using 1
  · exact funext (joinAt_line i y)
  · simp

lemma compact_slice_at (i : Fin (d+1)) (f : Space (d+1) → ℝ)
    (hs : HasCompactSupport f) (y : Space d) :
    HasCompactSupport (fun t : ℝ => f (joinAt i t y)) := by
  have hc : IsCompact ((fun x : Space (d+1) => x i) '' tsupport f) := hs.image (by fun_prop)
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro t ht
  exact ⟨joinAt i t y,subset_tsupport f ht,joinAt_same i t y⟩

noncomputable def coordinateStein (i : Fin (d+1))
    (f : Space (d+1) → ℝ) (x : Space (d+1)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin (d+1)) ℝ i)-x i*f x

lemma coordinateStein_continuous (i : Fin (d+1)) (f : Space (d+1) → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (coordinateStein i f) := by
  have hc := hf.continuous
  have hd := hf.continuous_fderiv one_ne_zero
  unfold coordinateStein
  fun_prop

lemma coordinateStein_compact (i : Fin (d+1)) (f : Space (d+1) → ℝ)
    (hs : HasCompactSupport f) : HasCompactSupport (coordinateStein i f) := by
  apply hs.mono'
  intro x hx
  by_contra he
  have hz : f x = 0 := Function.notMem_support.mp (fun h => he (subset_tsupport _ h))
  apply hx
  simp [coordinateStein,fderiv_of_notMem_tsupport ℝ he,hz]

theorem gaussian_coordinate_stein (i : Fin (d+1))
    (f : Space (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    (∫ x,coordinateStein i f x ∂gaussian (d+1)) = 0 := by
  have hi : Integrable (coordinateStein i f) (gaussian (d+1)) :=
    (coordinateStein_continuous i f hf).integrable_of_hasCompactSupport (coordinateStein_compact i f hs)
  have hm := gaussian_joinAt_swapped_preserving i
  have hip : Integrable (fun z : Space d × ℝ => coordinateStein i f (joinAt i z.2 z.1))
      ((gaussian d).prod (gaussianReal 0 1)) := hm.integrable_comp_of_integrable hi
  have he : (∫ x,coordinateStein i f x ∂gaussian (d+1)) =
      ∫ z : Space d × ℝ,coordinateStein i f (joinAt i z.2 z.1)
        ∂(gaussian d).prod (gaussianReal 0 1) := by
    rw [← hm.map_eq,integral_map hm.measurable.aemeasurable
      (coordinateStein_continuous i f hf).aestronglyMeasurable]
  rw [he,integral_prod _ hip]
  have hy (y : Space d) : (∫ t,coordinateStein i f (joinAt i t y) ∂gaussianReal 0 1) = 0 := by
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
  simp only [hy,integral_zero]

end GaussianMeasureBridge
