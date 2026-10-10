import GaussianTailCalculus
import GaussianScoreDerivative

/-! Price derivatives of actual Gaussian polyhedral epigraph masses. The
coefficients are exposed-face Gaussian-density integrals, derived by slicing. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def graphMass (v : Fin k → Space d) (b : Fin k → ℝ) : ℝ :=
  ((gaussian d).prod (gaussianReal 0 1)).real {z : Space d × ℝ | scoreMax v b z.1 < z.2}

lemma graphMass_eq_tail (v : Fin k → Space d) (b : Fin k → ℝ) :
    graphMass v b = ∫ y, standardTail (scoreMax v b y) ∂gaussian d := by
  let s : Set (Space d × ℝ) := {z | scoreMax v b z.1 < z.2}
  have hs : MeasurableSet s := measurableSet_lt
    ((continuous_scoreMax v b).measurable.comp measurable_fst) measurable_snd
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ)))
      ((gaussian d).prod (gaussianReal 0 1)) := (integrable_const _).indicator hs
  have he : graphMass v b = ∫ z, s.indicator (fun _ => (1 : ℝ)) z
      ∂(gaussian d).prod (gaussianReal 0 1) := by
    symm
    simpa [graphMass,s] using integral_indicator_const (μ := (gaussian d).prod (gaussianReal 0 1))
      (1 : ℝ) hs
  rw [he, integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    have heq : (fun x : ℝ => s.indicator (fun _ => (1 : ℝ)) (y,x)) =
        (Ioi (scoreMax v b y)).indicator (fun _ => (1 : ℝ)) := by
      ext x
      by_cases hx : scoreMax v b y < x <;> simp [s,hx]
    rw [heq]
    simpa [standardTail] using integral_indicator_const (μ := gaussianReal 0 1)
      (1 : ℝ) (measurableSet_Ioi (a := scoreMax v b y))

lemma integrable_tail_score (v : Fin k → Space d) (b : Fin k → ℝ) :
    Integrable (fun y => standardTail (scoreMax v b y)) (gaussian d) := by
  apply (integrable_const (1 : ℝ)).mono'
    (standardTail_lipschitz.continuous.comp (continuous_scoreMax v b)).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    change ‖standardTail (scoreMax v b y)‖ ≤ 1
    rw [standardTail, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

theorem graphMass_price_derivative (v : Fin k → Space d) (b q : Fin k → ℝ)
    (hv : Function.Injective v) :
    HasDerivAt (fun t => graphMass v (affinePrices b q t))
      (∑ i, q i * ∫ y in winningCell v b i, standardDensity (⟪v i, y⟫ - b i) ∂gaussian d) 0 := by
  have hzero (t : ℝ) : affineScores v (0 : Fin k → Space d) t = v := by
    funext i
    simp [affineScores]
  let g : Space d → ℝ := fun y => ∑ i, (winningCell v b i).indicator
    (fun y => q i * standardDensity (⟪v i, y⟫ - b i)) y
  have hgint : Integrable g (gaussian d) := integrable_finsetSum _ fun i _ =>
    ((integrable_standardDensity_comp (gaussian d) _ (by fun_prop)).const_mul (q i)).indicator
      (measurableSet_winningCell v b i)
  have hdiff : ∀ᵐ y ∂gaussian d, HasDerivAt
      (fun t => standardTail (scoreMax v (affinePrices b q t) y)) (g y) 0 := by
    filter_upwards [ae_unique_winner v b hv] with y hy
    obtain ⟨r, hr⟩ := hy
    have hnot : ∀ j, j ≠ r → y ∉ winningCell v b j := by
      intro j hj hyj
      exact Set.disjoint_left.mp (winningCell_disjoint v b j r hj) hyj hr
    have he : g y = q r * standardDensity (⟪v r, y⟫ - b r) := by
      dsimp only [g]
      rw [Finset.sum_eq_single r]
      · simp [hr]
      · intro j _ hj; simp [hnot j hj]
      · simp
    have hd : HasDerivAt (fun t => scoreMax v (affinePrices b q t) y) (-q r) 0 := by
      have h := affineScore_hasDerivAt v 0 b q y r hr
      simp only [hzero, Pi.zero_apply, inner_zero_left, zero_sub] at h
      exact h
    have hc := (standardTail_hasDerivAt (scoreMax v (affinePrices b q 0) y)).comp (0 : ℝ) hd
    simp only [affinePrices_zero] at hc
    rw [scoreMax_eq_winning_score v b y r hr] at hc
    rw [he]
    convert hc using 1
    · rfl
    · ring
  have hl (y : Space d) : LipschitzWith (Real.nnabs (standardDensity 0 * ‖q‖))
      (fun t => standardTail (scoreMax v (affinePrices b q t) y)) := by
    have hscore : LipschitzWith (Real.nnabs ‖q‖)
        (fun t => scoreMax v (affinePrices b q t) y) := by
      simpa only [hzero, norm_zero, zero_mul, zero_add] using affineScore_lipschitz v 0 b q y
    have h := standardTail_lipschitz.comp hscore
    convert h using 1
    · apply Subtype.ext
      change |standardDensity 0 * ‖q‖| = standardDensity 0 * |‖q‖|
      rw [abs_mul, abs_of_pos (standardDensity_pos 0)]
    · rfl
  have result := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := gaussian d) (F := fun t y => standardTail (scoreMax v (affinePrices b q t) y))
    (F' := g) (bound := fun _ => standardDensity 0 * ‖q‖) (s := Set.univ) (x₀ := 0)
    (by simp) (Eventually.of_forall fun t =>
      (standardTail_lipschitz.continuous.comp (continuous_scoreMax _ _)).aestronglyMeasurable)
    (by simpa using integrable_tail_score v b) hgint.aestronglyMeasurable
    (ae_of_all _ fun y => (hl y).lipschitzOnWith) (integrable_const _) hdiff
  have heval : (∫ y, g y ∂gaussian d) =
      ∑ i, q i * ∫ y in winningCell v b i, standardDensity (⟪v i, y⟫ - b i) ∂gaussian d := by
    rw [show g = (fun y => ∑ i, (winningCell v b i).indicator
      (fun y => q i * standardDensity (⟪v i, y⟫ - b i)) y) from rfl,
      integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (measurableSet_winningCell v b i), integral_const_mul]
    · intro i _
      exact ((integrable_standardDensity_comp (gaussian d) _ (by fun_prop)).const_mul (q i)).indicator
        (measurableSet_winningCell v b i)
  rw [heval] at result
  simpa only [graphMass_eq_tail] using result.2

end GaussianMeasureBridge
