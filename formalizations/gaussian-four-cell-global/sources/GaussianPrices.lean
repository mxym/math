import GaussianPartition
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FieldSimp

/-! Actual Gaussian score-price objective, including existence of a minimizer.
The minimizer theorem below is not yet a balancing-cell theorem: the latter
also requires proving the actual integral's price derivative under no ties. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def expectedScore (v : Fin k → Space d) (b : Fin k → ℝ) : ℝ :=
  ∫ x, scoreMax v b x ∂gaussian d

noncomputable def priceObjective (v : Fin k → Space d) (p b : Fin k → ℝ) : ℝ :=
  expectedScore v b + ∑ i, p i * b i

theorem integral_score (v : Space d) (b : ℝ) :
    (∫ x, ⟪v, x⟫ - b ∂gaussian d) = -b := by
  have hi : Integrable (fun x : Space d => ⟪v, x⟫) (gaussian d) := by
    simpa only [innerSL_apply_apply, id_eq] using
      ((innerSL ℝ v).integrable_comp (IsGaussian.integrable_id (μ := gaussian d)))
  have hz : (∫ x : Space d, ⟪v, x⟫ ∂gaussian d) = 0 := by
    simpa [gaussian, integral_id_stdGaussian] using
      (innerSL ℝ v).integral_comp_comm (IsGaussian.integrable_id (μ := gaussian d))
  rw [integral_sub hi (integrable_const b), hz]
  simp

lemma scoreMax_le_add_norm (v : Fin k → Space d) (b c : Fin k → ℝ) (x : Space d) :
    scoreMax v b x ≤ scoreMax v c x + ‖b - c‖ := by
  unfold scoreMax
  refine Finset.sup'_le _ _ fun i _ => ?_
  change ⟪v i, x⟫ - b i ≤ scoreMax v c x + ‖b - c‖
  have h1 := le_scoreMax v c x i
  have h2 : c i - b i ≤ ‖b - c‖ := by
    calc
      c i - b i ≤ |c i - b i| := le_abs_self _
      _ = ‖(b - c) i‖ := by simp [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ‖b - c‖ := norm_le_pi_norm _ i
  linarith

lemma scoreMax_abs_sub_le (v : Fin k → Space d) (b c : Fin k → ℝ) (x : Space d) :
    |scoreMax v b x - scoreMax v c x| ≤ ‖b - c‖ := by
  have h1 := scoreMax_le_add_norm v b c x
  have h2 := scoreMax_le_add_norm v c b x
  rw [norm_sub_rev c b] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem expectedScore_lipschitz (v : Fin k → Space d) :
    LipschitzWith 1 (expectedScore v) := by
  refine LipschitzWith.of_dist_le_mul fun b c => ?_
  have h : ‖∫ x, scoreMax v b x - scoreMax v c x ∂gaussian d‖ ≤ ‖b - c‖ := by
    have hb : ∀ᵐ x ∂gaussian d,
        ‖scoreMax v b x - scoreMax v c x‖ ≤ ‖b - c‖ :=
      ae_of_all (gaussian d) fun x => by
        simpa only [Real.norm_eq_abs] using scoreMax_abs_sub_le v b c x
    simpa using norm_integral_le_of_norm_le_const hb
  rw [integral_sub (integrable_scoreMax v b) (integrable_scoreMax v c)] at h
  simpa only [expectedScore, dist_eq_norm, NNReal.coe_one, one_mul] using h

theorem continuous_priceObjective (v : Fin k → Space d) (p : Fin k → ℝ) :
    Continuous (priceObjective v p) := by
  exact (expectedScore_lipschitz v).continuous.add
    (continuous_finsetSum _ fun i _ => by fun_prop)

lemma scoreMax_sub_const (v : Fin k → Space d) (b : Fin k → ℝ) (a : ℝ)
    (x : Space d) : scoreMax v (fun i => b i - a) x = scoreMax v b x + a := by
  apply le_antisymm
  · unfold scoreMax
    exact Finset.sup'_le _ _ fun i _ => by
      change ⟪v i, x⟫ - (b i - a) ≤ scoreMax v b x + a
      have h := le_scoreMax v b x i
      linarith
  · have h : scoreMax v b x ≤ scoreMax v (fun i => b i - a) x - a := by
      unfold scoreMax
      exact Finset.sup'_le _ _ fun i _ => by
        change ⟪v i, x⟫ - b i ≤ scoreMax v (fun i => b i - a) x - a
        have h := le_scoreMax v (fun i => b i - a) x i
        linarith
    linarith

theorem priceObjective_sub_const (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hp : ∑ i, p i = 1) (a : ℝ) :
    priceObjective v p (fun i => b i - a) = priceObjective v p b := by
  unfold priceObjective expectedScore
  simp_rw [scoreMax_sub_const, mul_sub]
  rw [integral_add (integrable_scoreMax v b) (integrable_const a)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp]
  simp

lemma expectedScore_nonneg_of_zero (v : Fin k → Space d) (b : Fin k → ℝ)
    (i : Fin k) (hi : b i = 0) : 0 ≤ expectedScore v b := by
  have h := integral_mono (integrable_score (v i) (b i)) (integrable_scoreMax v b)
    (fun x => le_scoreMax v b x i)
  rw [integral_score, hi, neg_zero] at h
  exact h

lemma weighted_price_le_objective (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hz : ∃ i, b i = 0) : ∑ i, p i * b i ≤ priceObjective v p b := by
  obtain ⟨i, hi⟩ := hz
  have h := expectedScore_nonneg_of_zero v b i hi
  unfold priceObjective
  linarith

/-- The actual Gaussian price objective has a global minimizer for all strictly
positive prescribed masses. No claim about a.e. winning labels is used here. -/
theorem exists_price_minimizer (v : Fin k → Space d) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ b : Fin k → ℝ, ∀ c, priceObjective v p b ≤ priceObjective v p c := by
  classical
  obtain ⟨r, hr⟩ := Finite.exists_min p
  let pmin : ℝ := p r
  have hpmin : 0 < pmin := hp r
  let f0 : ℝ := priceObjective v p 0
  have hf0 : 0 ≤ f0 := by
    have h := expectedScore_nonneg_of_zero v (0 : Fin k → ℝ) r rfl
    simpa [f0, priceObjective] using h
  let C : ℝ := f0 / pmin + 1
  have hC : 0 ≤ C := by positivity
  let S : Set (Fin k → ℝ) := Set.Icc 0 (fun _ => C)
  have hS : IsCompact S := isCompact_Icc
  have hzero : (0 : Fin k → ℝ) ∈ S := by
    exact ⟨le_rfl, fun i => hC⟩
  obtain ⟨b, hb, hmin⟩ := hS.exists_isMinOn ⟨0, hzero⟩
    (continuous_priceObjective v p).continuousOn
  refine ⟨b, fun c => ?_⟩
  have hb0 : priceObjective v p b ≤ f0 := hmin hzero
  by_cases hlarge : f0 ≤ priceObjective v p c
  · exact hb0.trans hlarge
  · obtain ⟨s, hsc⟩ := Finite.exists_min c
    let c' : Fin k → ℝ := fun i => c i - c s
    have hc' : ∀ i, 0 ≤ c' i := fun i => sub_nonneg.mpr (hsc i)
    have hshift : priceObjective v p c' = priceObjective v p c :=
      priceObjective_sub_const v p c hs (c s)
    have hweighted : ∑ i, p i * c' i ≤ priceObjective v p c' :=
      weighted_price_le_objective v p c' ⟨s, sub_self _⟩
    have hsub : ∀ i, pmin * c' i ≤ f0 := by
      intro i
      calc
        pmin * c' i ≤ p i * c' i := mul_le_mul_of_nonneg_right (hr i) (hc' i)
        _ ≤ ∑ j, p j * c' j := Finset.single_le_sum
          (fun j _ => mul_nonneg (hp j).le (hc' j)) (Finset.mem_univ i)
        _ ≤ priceObjective v p c' := hweighted
        _ ≤ f0 := by rw [hshift]; exact (not_le.mp hlarge).le
    have hcS : c' ∈ S := by
      refine ⟨hc', fun i => ?_⟩
      have hi : c' i ≤ f0 / pmin := by
        apply (le_div_iff₀ hpmin).mpr
        simpa only [mul_comm] using hsub i
      exact hi.trans (by dsimp [C]; linarith)
    rw [← hshift]
    exact hmin hcS

end GaussianMeasureBridge
