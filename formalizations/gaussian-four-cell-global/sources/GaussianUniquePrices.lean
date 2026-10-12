import GaussianWinningPartition
import GaussianFullSupport
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Uniqueness of actual balanced Gaussian prices modulo common shift.
The proof uses a continuous Jensen gap, actual full support, and connectedness;
it does not postulate a facet Hessian or its definiteness. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def priceMid (b c : Fin k → ℝ) : Fin k → ℝ := fun i => (b i + c i) / 2

lemma scoreMid_le (v : Fin k → Space d) (b c : Fin k → ℝ) (x : Space d) :
    2 * scoreMax v (priceMid b c) x ≤ scoreMax v b x + scoreMax v c x := by
  have h : scoreMax v (priceMid b c) x ≤ (scoreMax v b x + scoreMax v c x) / 2 := by
    unfold scoreMax
    refine Finset.sup'_le _ _ fun i _ => ?_
    change ⟪v i, x⟫ - (b i + c i) / 2 ≤ (scoreMax v b x + scoreMax v c x) / 2
    have hb := le_scoreMax v b x i
    have hc := le_scoreMax v c x i
    linarith
  linarith

lemma weighted_priceMid (p b c : Fin k → ℝ) :
    2 * (∑ i, p i * priceMid b c i) = (∑ i, p i * b i) + ∑ i, p i * c i := by
  have h : ∀ i, p i * priceMid b c i = (p i * b i + p i * c i) / 2 := by
    intro i
    unfold priceMid
    ring
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

theorem minimizers_jensen_gap_zero (v : Fin k → Space d) (p b c : Fin k → ℝ)
    (hb : ∀ a, priceObjective v p b ≤ priceObjective v p a)
    (hc : ∀ a, priceObjective v p c ≤ priceObjective v p a) :
    ∀ x, scoreMax v b x + scoreMax v c x - 2 * scoreMax v (priceMid b c) x = 0 := by
  let g : Space d → ℝ := fun x =>
    scoreMax v b x + scoreMax v c x - 2 * scoreMax v (priceMid b c) x
  have hgint : Integrable g (gaussian d) :=
    ((integrable_scoreMax v b).add (integrable_scoreMax v c)).sub
      ((integrable_scoreMax v (priceMid b c)).const_mul 2)
  have hgcont : Continuous g :=
    ((continuous_scoreMax v b).add (continuous_scoreMax v c)).sub
      ((continuous_const.mul (continuous_scoreMax v (priceMid b c))))
  have hgnonneg : 0 ≤ g := fun x => sub_nonneg.mpr (scoreMid_le v b c x)
  have hgeval : (∫ x, g x ∂gaussian d) =
      priceObjective v p b + priceObjective v p c - 2 * priceObjective v p (priceMid b c) := by
    dsimp [g]
    have hadd : Integrable (fun x => scoreMax v b x + scoreMax v c x) (gaussian d) :=
      (integrable_scoreMax v b).add (integrable_scoreMax v c)
    have hmul : Integrable (fun x => 2 * scoreMax v (priceMid b c) x) (gaussian d) :=
      (integrable_scoreMax v (priceMid b c)).const_mul 2
    rw [integral_sub hadd hmul]
    rw [integral_add (integrable_scoreMax v b) (integrable_scoreMax v c), integral_const_mul]
    have hs := weighted_priceMid p b c
    unfold priceObjective expectedScore
    linarith
  have hgle : (∫ x, g x ∂gaussian d) ≤ 0 := by
    rw [hgeval]
    have h1 := hb c
    have h2 := hc b
    have h3 := hb (priceMid b c)
    linarith
  intro x
  by_contra hx
  exact (not_lt_of_ge hgle)
    (integral_pos_of_integrable_nonneg_nonzero hgcont hgint hgnonneg hx)

lemma common_maximizer_of_jensen_zero (v : Fin k → Space d) (b c : Fin k → ℝ)
    (x : Space d)
    (hx : scoreMax v b x + scoreMax v c x - 2 * scoreMax v (priceMid b c) x = 0) :
    ∃ i, scoreMax v b x = ⟪v i, x⟫ - b i ∧ scoreMax v c x = ⟪v i, x⟫ - c i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i : Fin k => ⟪v i, x⟫ - priceMid b c i)
  have hmid : scoreMax v (priceMid b c) x = ⟪v i, x⟫ - priceMid b c i := by
    refine le_antisymm ?_ (le_scoreMax v _ x i)
    unfold scoreMax
    exact Finset.sup'_le _ _ fun j _ => hi j
  rw [hmid] at hx
  have hb := le_scoreMax v b x i
  have hc := le_scoreMax v c x i
  dsimp [priceMid] at hx
  refine ⟨i, ?_, ?_⟩ <;> linarith

theorem minimizers_score_difference_constant (v : Fin k → Space d) (p b c : Fin k → ℝ)
    (hb : ∀ a, priceObjective v p b ≤ priceObjective v p a)
    (hc : ∀ a, priceObjective v p c ≤ priceObjective v p a) :
    ∃ a : ℝ, ∀ x, scoreMax v b x - scoreMax v c x = a := by
  let D : Space d → ℝ := fun x => scoreMax v b x - scoreMax v c x
  let T : Set ℝ := Set.range (fun i : Fin k => c i - b i)
  have hT : T.Finite := Set.finite_range _
  have hmaps : Set.MapsTo D Set.univ T := by
    intro x _
    obtain ⟨i, hbi, hci⟩ := common_maximizer_of_jensen_zero v b c x
      (minimizers_jensen_gap_zero v p b c hb hc x)
    refine ⟨i, ?_⟩
    dsimp [D]
    rw [hbi, hci]
    ring
  have hcont : Continuous D := (continuous_scoreMax v b).sub (continuous_scoreMax v c)
  obtain ⟨a, _, ha⟩ := (isPreconnected_univ : IsPreconnected (Set.univ : Set (Space d))).eqOn_const_of_mapsTo
    hT.isDiscrete hcont.continuousOn hmaps (Set.range_nonempty _)
  exact ⟨a, fun x => ha (Set.mem_univ x)⟩

/-- All strictly positive masses and distinct vectors: any two actual balancing
price vectors differ by one common additive constant. -/
theorem balancing_prices_unique_mod_const (v : Fin k → Space d) (p b c : Fin k → ℝ)
    (hv : Function.Injective v) (hp : ∀ i, 0 < p i)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = p i)
    (hc : ∀ i, (gaussian d).real (winningCell v c i) = p i) :
    ∃ a : ℝ, ∀ i, c i = b i + a := by
  obtain ⟨a, ha⟩ := minimizers_score_difference_constant v p b c
    (balanced_price_is_minimizer v p b hv hb) (balanced_price_is_minimizer v p c hv hc)
  refine ⟨a, fun i => ?_⟩
  have hne : (winningCell v b i).Nonempty := by
    by_contra h
    have he : winningCell v b i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hm := hb i
    rw [he, measureReal_empty] at hm
    exact (ne_of_gt (hp i)) hm.symm
  obtain ⟨x, hxi⟩ := hne
  obtain ⟨r, hbr, hcr⟩ := common_maximizer_of_jensen_zero v b c x
    (minimizers_jensen_gap_zero v p b c
      (balanced_price_is_minimizer v p b hv hb) (balanced_price_is_minimizer v p c hv hc) x)
  have hri : r = i := by
    by_contra h
    have hlt := hxi r h
    have hle := le_scoreMax v b x i
    rw [hbr] at hle
    linarith
  subst r
  have heq := ha x
  rw [hbr, hcr] at heq
  linarith

end GaussianMeasureBridge
