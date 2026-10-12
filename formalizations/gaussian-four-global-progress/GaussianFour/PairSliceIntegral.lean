import GaussianFour.PairSlice

/-! Fubini and dominated differentiation for a price-shifted winning cell.
The integration uses the actual Gaussian product decomposition. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

noncomputable def pairSliceValue (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (t : ℝ) (y : Space d) : ℝ :=
  maskedTail (pairSliceMask v b i j y) (pairHeight v b i j y-t/pairDen v i j)

lemma pairSliceValue_eq_gaussian_integral
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j) (t : ℝ) (y : Space d) :
    pairSliceValue v b i j t y = ∫ s, (winningCell v (coordinateShift b j t) i).indicator
      (fun _ => (1 : ℝ)) (joinCoordinate s y) ∂gaussianReal 0 1 := by
  classical
  rw [pairSliceValue, maskedTail_eq_gaussian_integral]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    dsimp only
    have he := pair_winning_coordinateShift_iff v b i j hij hden t s y
    by_cases hw : joinCoordinate s y ∈ winningCell v (coordinateShift b j t) i
    · rw [indicator_of_mem hw, indicator_of_mem (he.mp hw)]
    · rw [indicator_of_notMem hw, indicator_of_notMem (fun h => hw (he.mpr h))]

lemma measurable_pairSliceValue
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j) (t : ℝ) : Measurable (pairSliceValue v b i j t) := by
  have hm : Measurable (fun z : Space d × ℝ =>
      (winningCell v (coordinateShift b j t) i).indicator (fun _ => (1 : ℝ))
        (joinCoordinate z.2 z.1)) :=
    (measurable_const.indicator (measurableSet_winningCell _ _ _)).comp
      gaussian_joinCoordinate_swapped_preserving.measurable
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)
  convert h.measurable using 1
  funext y
  exact pairSliceValue_eq_gaussian_integral v b i j hij hden t y

lemma integrable_pairSliceValue
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j) (t : ℝ) :
    Integrable (pairSliceValue v b i j t) (gaussian d) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_pairSliceValue v b i j hij hden t).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    rw [pairSliceValue, Real.norm_eq_abs, abs_of_nonneg (maskedTail_nonneg _ _)]
    exact maskedTail_le_one _ (measurableSet_pairSliceMask v b i j y) _

/-- Exact slicing of the original winning-cell mass, not a replacement model. -/
theorem winningMass_eq_pairSliceIntegral
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j) (t : ℝ) :
    winningMass v (coordinateShift b j t) i =
      ∫ y, pairSliceValue v b i j t y ∂gaussian d := by
  classical
  let S := (fun z : Space d × ℝ => joinCoordinate z.2 z.1) ⁻¹'
    winningCell v (coordinateShift b j t) i
  have hS : MeasurableSet S := (measurableSet_winningCell _ _ _).preimage
    gaussian_joinCoordinate_swapped_preserving.measurable
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ)))
      ((gaussian d).prod (gaussianReal 0 1)) := (integrable_const _).indicator hS
  have hp := gaussian_joinCoordinate_swapped_preserving.measureReal_preimage
    (measurableSet_winningCell v (coordinateShift b j t) i).nullMeasurableSet
  have he : winningMass v (coordinateShift b j t) i =
      ∫ z, S.indicator (fun _ => (1 : ℝ)) z ∂(gaussian d).prod (gaussianReal 0 1) := by
    rw [integral_indicator_const (1 : ℝ) hS]
    simpa only [smul_eq_mul, mul_one, winningMass] using hp.symm
  rw [he, integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    rw [pairSliceValue_eq_gaussian_integral v b i j hij hden t y]
    apply integral_congr_ae
    exact ae_of_all _ fun s => by
      by_cases hx : joinCoordinate s y ∈ winningCell v (coordinateShift b j t) i <;>
        simp [S, hx]

lemma pairSliceValue_lipschitz
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k)
    (hden : 0 < pairDen v i j) (y : Space d) :
    LipschitzWith ⟨standardDensity 0 / pairDen v i j,
      div_nonneg (standardDensity_pos 0).le hden.le⟩ (fun t => pairSliceValue v b i j t y) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  have h := (maskedTail_lipschitz _ (measurableSet_pairSliceMask v b i j y)).dist_le_mul
    (pairHeight v b i j y-t/pairDen v i j) (pairHeight v b i j y-u/pairDen v i j)
  have he : dist (pairHeight v b i j y-t/pairDen v i j)
      (pairHeight v b i j y-u/pairDen v i j) = dist t u / pairDen v i j := by
    rw [Real.dist_eq, Real.dist_eq,
      show (pairHeight v b i j y-t/pairDen v i j) -
        (pairHeight v b i j y-u/pairDen v i j) = (u-t)/pairDen v i j by ring,
      abs_div, abs_of_pos hden, abs_sub_comm]
  change dist (pairSliceValue v b i j t y) (pairSliceValue v b i j u y) ≤
    standardDensity 0 * dist _ _ at h
  rw [he] at h
  change dist (pairSliceValue v b i j t y) (pairSliceValue v b i j u y) ≤
    (standardDensity 0 / pairDen v i j) * dist t u
  convert h using 1 <;> ring

lemma pairSlice_boundary_density
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (y : Space d) :
    (pairSliceMask v b i j y).indicator standardDensity (pairHeight v b i j y) =
      (affineMask (facetIndices i j) (facetNormal v i j) (facetOffset v b i j)).indicator
        (fun y => standardDensity (pairHeight v b i j y)) y := by
  classical
  have he := pairSliceMask_boundary_iff v b i j y
  by_cases hx : pairHeight v b i j y ∈ pairSliceMask v b i j y
  · rw [indicator_of_mem hx, indicator_of_mem (he.mp hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (he.mpr h))]

lemma pairSliceValue_hasDerivAt
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (y : Space d)
    (hc : ContinuousAt ((pairSliceMask v b i j y).indicator standardDensity)
      (pairHeight v b i j y)) :
    HasDerivAt (fun t => pairSliceValue v b i j t y)
      ((pairSliceMask v b i j y).indicator standardDensity (pairHeight v b i j y) /
        pairDen v i j) 0 := by
  have hd := maskedTail_hasDerivAt _ (measurableSet_pairSliceMask v b i j y) _ hc
  have hl : HasDerivAt (fun t : ℝ => pairHeight v b i j y-t/pairDen v i j)
      (-(1 / pairDen v i j)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const (pairDen v i j)).const_sub (pairHeight v b i j y)
  have hh : HasDerivAt (maskedTail (pairSliceMask v b i j y))
      (- (pairSliceMask v b i j y).indicator standardDensity (pairHeight v b i j y))
      (pairHeight v b i j y-(0 : ℝ)/pairDen v i j) := by
    simpa only [zero_div, sub_zero] using hd
  convert hh.comp 0 hl using 1
  · rfl
  · ring

end GaussianFour
