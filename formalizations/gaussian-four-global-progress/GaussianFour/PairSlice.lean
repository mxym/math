import GaussianFour.MaskedTail
import GaussianFour.FacetChart
import GaussianWinningMassDerivative

/-! Exact one-coordinate slicing for a single moving competitor price.
The other inequalities are retained as a measurable mask, with no epigraph
or affine-independence assumption on the complete diagram. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

def pairSliceMask (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (y : Space d) : Set ℝ :=
  {s | ∀ l ∈ facetIndices i j,
    0 < (⟪v i, joinCoordinate s y⟫ - b i) - (⟪v l, joinCoordinate s y⟫ - b l)}

lemma measurableSet_pairSliceMask (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (y : Space d) : MeasurableSet (pairSliceMask v b i j y) := by
  unfold pairSliceMask
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (by simp only [inner_coordinate_split]; fun_prop)

lemma pairSliceMask_boundary_iff (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (y : Space d) :
    pairHeight v b i j y ∈ pairSliceMask v b i j y ↔
      y ∈ affineMask (facetIndices i j) (facetNormal v i j) (facetOffset v b i j) := by
  unfold pairSliceMask affineMask
  change (∀ l ∈ facetIndices i j, 0 < (⟪v i, joinCoordinate (pairHeight v b i j y) y⟫ - b i) - (⟪v l, joinCoordinate (pairHeight v b i j y) y⟫ - b l)) ↔ _
  simp_rw [pairHeight_score_gap, sub_pos]
  rfl

lemma pair_score_gap_eq_mul (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (hden : pairDen v i j ≠ 0) (s : ℝ) (y : Space d) :
    (⟪v i, joinCoordinate s y⟫ - b i) - (⟪v j, joinCoordinate s y⟫ - b j) =
      pairDen v i j * (s-pairHeight v b i j y) := by
  have ht := pairHeight_tie v b i j hden y
  simp only [inner_coordinate_split] at ht ⊢
  unfold pairDen
  nlinarith

/-- Changing only competitor j moves just one cutoff in the fixed pair chart. -/
theorem pair_winning_coordinateShift_iff
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : 0 < pairDen v i j) (t s : ℝ) (y : Space d) :
    joinCoordinate s y ∈ winningCell v (coordinateShift b j t) i ↔
      s ∈ Ioi (pairHeight v b i j y - t/pairDen v i j) ∩ pairSliceMask v b i j y := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have hfactor : pairDen v i j * (s-pairHeight v b i j y) + t =
      pairDen v i j * (s-(pairHeight v b i j y-t/pairDen v i j)) := by
    field_simp [hden.ne']
    <;> ring
  have hcut : (⟪v j, joinCoordinate s y⟫ - coordinateShift b j t j <
      ⟪v i, joinCoordinate s y⟫ - coordinateShift b j t i) ↔
      pairHeight v b i j y-t/pairDen v i j < s := by
    simp only [coordinateShift, hij, ↓reduceIte, add_zero]
    have hg := pair_score_gap_eq_mul v b i j hden.ne' s y
    have he : (⟪v i, joinCoordinate s y⟫-b i) -
        (⟪v j, joinCoordinate s y⟫-(b j+t)) =
        pairDen v i j * (s-(pairHeight v b i j y-t/pairDen v i j)) := by
      linarith [hfactor]
    rw [← sub_pos, he, mul_pos_iff_of_pos_left hden, sub_pos]
  constructor
  · intro hw
    refine ⟨hcut.mp (hw j hji), ?_⟩
    intro l hl
    have hn : l ≠ i ∧ l ≠ j := by simpa [facetIndices] using hl
    have h := hw l hn.1
    simpa only [coordinateShift, hn.2, hij, ↓reduceIte, add_zero, sub_pos] using h
  · rintro ⟨hc,hm⟩ l hli
    by_cases hlj : l = j
    · subst l; exact hcut.mpr hc
    · have hl : l ∈ facetIndices i j := by simp [facetIndices, hli, hlj]
      have h := hm l hl
      simpa only [coordinateShift, hlj, hij, ↓reduceIte, add_zero, sub_pos] using h

/-- At almost every point of the tie chart all remaining inequalities are
locally stable, even when their restricted linear parts vanish. -/
theorem ae_pairSliceMask_density_continuous
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j)
    (hden : pairDen v i j ≠ 0)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l)) :
    ∀ᵐ y ∂gaussian d, ContinuousAt ((pairSliceMask v b i j y).indicator standardDensity)
      (pairHeight v b i j y) := by
  classical
  have hne : ∀ᵐ y ∂gaussian d, ∀ l, l ∈ facetIndices i j →
      ⟪facetNormal v i j l,y⟫ ≠ facetOffset v b i j l := by
    apply ae_all_iff.mpr
    intro l
    by_cases hl : l ∈ facetIndices i j
    · have hn : l ≠ i ∧ l ≠ j := by simpa [facetIndices] using hl
      exact (ae_affine_ne _ _ (facet_restriction_nonzero v b i j l hij
        (Ne.symm hn.1) (Ne.symm hn.2) hden hmass)).mono fun y hy _ => hy
    · exact ae_of_all _ fun y h => False.elim (hl h)
  filter_upwards [hne] with y hy
  let a := pairHeight v b i j y
  let g := fun l s => (⟪v i,joinCoordinate s y⟫-b i) - (⟪v l,joinCoordinate s y⟫-b l)
  have he : ∀ᶠ s in 𝓝 a, ∀ l, l ∈ facetIndices i j → ((0 < g l s) ↔ (0 < g l a)) := by
    apply eventually_all.mpr
    intro l
    by_cases hl : l ∈ facetIndices i j
    · have hc : ContinuousAt (g l) a := by dsimp [g]; simp only [inner_coordinate_split]; fun_prop
      have hz : g l a ≠ 0 := by
        dsimp only [g,a]
        rw [pairHeight_score_gap]
        exact sub_ne_zero.mpr (hy l hl)
      by_cases hp : 0 < g l a
      · exact (continuousAt_const.eventually_lt hc hp).mono fun s hs _ => iff_of_true hs hp
      · have hm : g l a < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
        exact (hc.eventually_lt continuousAt_const hm).mono fun s hs _ =>
          iff_of_false (not_lt_of_ge hs.le) hp
    · exact Eventually.of_forall fun s h => False.elim (hl h)
  have heq : ∀ᶠ s in 𝓝 a, (s ∈ pairSliceMask v b i j y) ↔ (a ∈ pairSliceMask v b i j y) := by
    filter_upwards [he] with s hs
    exact forall_congr' fun l => forall_congr' fun hl => hs l hl
  by_cases ha : a ∈ pairSliceMask v b i j y
  · apply continuous_standardDensity.continuousAt.congr_of_eventuallyEq
    filter_upwards [heq] with s hs
    exact indicator_of_mem (hs.mpr ha) _
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [heq] with s hs
    exact indicator_of_notMem (fun h => ha (hs.mp h)) _

end GaussianFour
