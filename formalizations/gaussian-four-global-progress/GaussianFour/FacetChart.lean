import GaussianFour.AffineBoundary
import GaussianFour.TripleAffineExclusion
import GaussianWinningGraphFlux

/-! Fixed-coordinate charts of actual Gaussian winning facets. A pairwise tie
hyperplane is written as a graph. Restricted competitor inequalities can have
zero linear parts; positive cell masses exclude their being identically zero. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ}

noncomputable def pairDen (v : Fin k → Space (d+1)) (i j : Fin k) : ℝ :=
  v i 0 - v j 0

noncomputable def pairSlope (v : Fin k → Space (d+1)) (i j : Fin k) : Space d :=
  (pairDen v i j)⁻¹ • (tailCoordinates (v j) - tailCoordinates (v i))

noncomputable def pairPrice (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) : ℝ := (b j - b i) / pairDen v i j

noncomputable def pairHeight (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (y : Space d) : ℝ := ⟪pairSlope v i j, y⟫ - pairPrice v b i j

noncomputable def facetNormal (v : Fin k → Space (d+1)) (i j l : Fin k) : Space d :=
  tailCoordinates (v i) - tailCoordinates (v l) +
    (v i 0 - v l 0) • pairSlope v i j

noncomputable def facetOffset (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j l : Fin k) : ℝ := b i - b l + (v i 0 - v l 0) * pairPrice v b i j

def facetIndices (i j : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun l => l ≠ i ∧ l ≠ j)

noncomputable def pairChartDensity (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) : ℝ :=
  affineDensityIntegral (facetIndices i j) (facetNormal v i j)
    (facetOffset v b i j) (pairSlope v i j) (pairPrice v b i j)

noncomputable def pairChartWeight (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) : ℝ := pairChartDensity v b i j / |pairDen v i j|

lemma pairHeight_tie (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j : Fin k) (hden : pairDen v i j ≠ 0) (y : Space d) :
    ⟪v i, joinCoordinate (pairHeight v b i j y) y⟫ - b i =
      ⟪v j, joinCoordinate (pairHeight v b i j y) y⟫ - b j := by
  simp only [inner_coordinate_split, pairHeight, pairSlope, pairPrice,
    real_inner_smul_left, inner_sub_left]
  unfold pairDen at hden ⊢
  field_simp [hden]
  <;> ring

lemma pairHeight_score_gap (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j l : Fin k) (y : Space d) :
    (⟪v i, joinCoordinate (pairHeight v b i j y) y⟫ - b i) -
      (⟪v l, joinCoordinate (pairHeight v b i j y) y⟫ - b l) =
        ⟪facetNormal v i j l, y⟫ - facetOffset v b i j l := by
  simp only [inner_coordinate_split, facetNormal, facetOffset, pairHeight,
    inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

/-- No restricted competitor is identically zero on a valid chart of a
positive-mass winning diagram. This includes rank-one and rank-two scores. -/
theorem facet_restriction_nonzero (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hden : pairDen v i j ≠ 0)
    (hmass : ∀ t, 0 < (gaussian (d+1)).real (winningCell v b t)) :
    facetNormal v i j l ≠ 0 ∨ facetOffset v b i j l ≠ 0 := by
  by_cases hn : facetNormal v i j l = 0
  · right
    intro ho
    apply no_proportional_differences_of_positive_masses v b i j l hij hil hjl hmass
      ((v i 0 - v l 0) / pairDen v i j)
    intro x
    let y := tailCoordinates x
    let h := pairHeight v b i j y
    have hzero := pairHeight_score_gap v b i j l y
    rw [hn, ho, inner_zero_left, sub_zero] at hzero
    have htie := pairHeight_tie v b i j hden y
    have hsplit (t : Fin k) :
        ⟪v t, x⟫ = v t 0 * x 0 + ⟪tailCoordinates (v t), y⟫ := by
      simpa only [y, joinCoordinate_eta] using
        inner_coordinate_split (v t) (x 0) (tailCoordinates x)
    have he1 : (⟪v i,x⟫ - b i) - (⟪v l,x⟫ - b l) =
        (v i 0 - v l 0) * (x 0 - h) := by
      simp only [inner_coordinate_split] at hzero
      rw [hsplit i, hsplit l]
      dsimp only [h]
      nlinarith [hzero]
    have he2 : (⟪v i,x⟫ - b i) - (⟪v j,x⟫ - b j) =
        pairDen v i j * (x 0 - h) := by
      simp only [inner_coordinate_split] at htie
      rw [hsplit i, hsplit j]
      dsimp only [h, pairDen]
      nlinarith [htie]
    rw [he1, he2]
    field_simp [hden]
  · exact Or.inl hn

end GaussianFour
