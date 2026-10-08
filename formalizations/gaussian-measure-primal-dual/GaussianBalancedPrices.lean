import GaussianPrices
import GaussianNoTies
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Derivatives of actual Gaussian score integrals and balancing prices.
All winning probabilities are those of the actual `stdGaussian` measure. -/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def coordinateShift (b : Fin k → ℝ) (i : Fin k) (t : ℝ) : Fin k → ℝ :=
  fun j => b j + if j = i then t else 0

lemma coordinateShift_zero (b : Fin k → ℝ) (i : Fin k) : coordinateShift b i 0 = b := by
  funext j
  simp [coordinateShift]

lemma coordinateShift_dist_le (b : Fin k → ℝ) (i : Fin k) (s t : ℝ) :
    ‖coordinateShift b i s - coordinateShift b i t‖ ≤ |s - t| := by
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro j
  by_cases h : j = i <;> simp [coordinateShift, h, Real.norm_eq_abs]

lemma coordinateScore_lipschitz (v : Fin k → Space d) (b : Fin k → ℝ) (i : Fin k)
    (x : Space d) : LipschitzWith 1 (fun t => scoreMax v (coordinateShift b i t) x) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have h := (scoreMax_abs_sub_le v (coordinateShift b i s) (coordinateShift b i t) x).trans
    (coordinateShift_dist_le b i s t)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h

lemma scoreMax_eq_winning_score (v : Fin k → Space d) (b : Fin k → ℝ)
    (x : Space d) (r : Fin k) (hr : x ∈ winningCell v b r) :
    scoreMax v b x = ⟪v r, x⟫ - b r := by
  refine le_antisymm ?_ (le_scoreMax v b x r)
  unfold scoreMax
  refine Finset.sup'_le _ _ fun j _ => ?_
  by_cases h : j = r
  · simp [h]
  · exact (hr j h).le

lemma winningCell_disjoint (v : Fin k → Space d) (b : Fin k → ℝ) (i j : Fin k)
    (hij : i ≠ j) : Disjoint (winningCell v b i) (winningCell v b j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact (not_lt_of_gt (hxi j hij.symm)) (hxj i hij)

lemma coordinateScore_hasDerivAt (v : Fin k → Space d) (b : Fin k → ℝ)
    (i r : Fin k) (x : Space d) (hr : x ∈ winningCell v b r) :
    HasDerivAt (fun t => scoreMax v (coordinateShift b i t) x)
      (if r = i then -1 else 0) 0 := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), x ∈ winningCell v (coordinateShift b i t) r := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = r
    · exact Eventually.of_forall fun t h => False.elim (h hj)
    · have hcontj : ContinuousAt
          (fun t : ℝ => ⟪v j, x⟫ - coordinateShift b i t j) 0 := by
        by_cases hji : j = i <;> simp [coordinateShift, hji] <;> fun_prop
      have hcontr : ContinuousAt
          (fun t : ℝ => ⟪v r, x⟫ - coordinateShift b i t r) 0 := by
        by_cases hri : r = i <;> simp [coordinateShift, hri] <;> fun_prop
      have hlt := hcontj.eventually_lt hcontr (by
        simpa only [coordinateShift_zero] using hr j hj)
      exact hlt.mono fun t ht _ => ht
  have heq : (fun t => scoreMax v (coordinateShift b i t) x) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ⟪v r, x⟫ - coordinateShift b i t r) := by
    exact hevent.mono fun t ht => scoreMax_eq_winning_score v _ x r ht
  have hd : HasDerivAt (fun t : ℝ => ⟪v r, x⟫ - coordinateShift b i t r)
      (if r = i then -1 else 0) 0 := by
    by_cases h : r = i
    · subst r
      simpa [coordinateShift, sub_add_eq_sub_sub, Pi.sub_def] using
        (hasDerivAt_const (0 : ℝ) (⟪v i, x⟫ - b i)).sub (hasDerivAt_id 0)
    · simp only [coordinateShift, h, ↓reduceIte, add_zero]
      exact hasDerivAt_const _ _
  exact hd.congr_of_eventuallyEq heq

noncomputable def winnerDerivative (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (x : Space d) : ℝ := (winningCell v b i).indicator (fun _ => -1) x

theorem expectedScore_coordinate_derivative (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    HasDerivAt (fun t => expectedScore v (coordinateShift b i t))
      (-(gaussian d).real (winningCell v b i)) 0 := by
  have hdiff : ∀ᵐ x ∂gaussian d, HasDerivAt
      (fun t => scoreMax v (coordinateShift b i t) x) (winnerDerivative v b i x) 0 := by
    filter_upwards [ae_unique_winner v b hv] with x hx
    obtain ⟨r, hr⟩ := hx
    have h := coordinateScore_hasDerivAt v b i r x hr
    by_cases hri : r = i
    · subst r
      simpa [winnerDerivative, Set.indicator_of_mem hr] using h
    · have hxi : x ∉ winningCell v b i := by
        intro hx
        exact Set.disjoint_left.mp (winningCell_disjoint v b r i hri) hr hx
      simpa [winnerDerivative, Set.indicator_of_notMem hxi, hri] using h
  have hm : AEStronglyMeasurable (winnerDerivative v b i) (gaussian d) := by
    exact (stronglyMeasurable_const.indicator (measurableSet_winningCell v b i)).aestronglyMeasurable
  have hresult := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := gaussian d) (F := fun t x => scoreMax v (coordinateShift b i t) x)
    (F' := winnerDerivative v b i) (bound := fun _ => (1 : ℝ))
    (s := Set.univ) (x₀ := 0) (by simp)
    (Eventually.of_forall fun t => (continuous_scoreMax v _).aestronglyMeasurable)
    (by simpa only [coordinateShift_zero] using integrable_scoreMax v b)
    hm (ae_of_all _ fun x => by
      simpa using coordinateScore_lipschitz v b i x)
    (integrable_const 1) hdiff
  have heval : (∫ x, winnerDerivative v b i x ∂gaussian d) =
      -(gaussian d).real (winningCell v b i) := by
    simpa only [winnerDerivative, smul_eq_mul, mul_neg, mul_one] using
      integral_indicator_const (-1 : ℝ) (measurableSet_winningCell v b i)
  rw [heval] at hresult
  exact hresult.2

lemma weighted_price_coordinate (p b : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    (∑ j, p j * coordinateShift b i t j) = (∑ j, p j * b j) + p i * t := by
  classical
  simp [coordinateShift, mul_add, Finset.sum_add_distrib, mul_ite]

theorem priceObjective_coordinate_derivative (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    HasDerivAt (fun t => priceObjective v p (coordinateShift b i t))
      (p i - (gaussian d).real (winningCell v b i)) 0 := by
  simp only [priceObjective, weighted_price_coordinate]
  convert (expectedScore_coordinate_derivative v b hv i).add
    ((hasDerivAt_const (0 : ℝ) (∑ j, p j * b j)).add
      ((hasDerivAt_id 0).const_mul (p i))) using 1
  · funext t
    simp [add_assoc]
  · ring

/-- Distinct Gaussian score vectors and positive masses admit balancing prices.
This conclusion refers to the actual strictly winning measurable cells. -/
theorem exists_balancing_prices (v : Fin k → Space d) (p : Fin k → ℝ)
    (hv : Function.Injective v) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ b : Fin k → ℝ, ∀ i, (gaussian d).real (winningCell v b i) = p i := by
  obtain ⟨b, hb⟩ := exists_price_minimizer v p hp hs
  refine ⟨b, fun i => ?_⟩
  have hlocal : IsLocalMin (fun t => priceObjective v p (coordinateShift b i t)) 0 := by
    exact Eventually.of_forall fun t => by
      simpa only [coordinateShift_zero] using hb (coordinateShift b i t)
  have hz := hlocal.hasDerivAt_eq_zero (priceObjective_coordinate_derivative v p b hv i)
  linarith

end GaussianMeasureBridge
