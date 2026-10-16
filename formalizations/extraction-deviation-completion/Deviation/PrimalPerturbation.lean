import Deviation.EntropyPerturbation

open scoped BigOperators Topology
open Set Filter ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def uniformLaw : ι → ℝ := fun _ => (Fintype.card ι:ℝ)⁻¹

theorem uniformLaw_pos (i : ι) : 0 < uniformLaw i := by unfold uniformLaw; positivity

theorem uniformLaw_sum : ∑ i : ι, uniformLaw i = 1 := by
  simp only [uniformLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

theorem divergence_uniformLaw (q : ι → ℝ) (hqs : ∑ i, q i = 1) :
    divergence q (uniformLaw (ι := ι)) = Real.log (Fintype.card ι)-entropy q := by
  unfold divergence entropy finiteMean selfInformation uniformLaw
  simp only [Real.log_inv, sub_neg_eq_add, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hqs, one_mul, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The finite entropy maximum is strict at every nonuniform law, including
laws with zero coordinates. This is derived from the strict Gibbs inequality. -/
theorem entropy_lt_log_card_of_ne_uniform (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hqs : ∑ i, q i = 1) (hne : q ≠ uniformLaw) :
    entropy q < Real.log (Fintype.card ι) := by
  have h := divergence_pos_of_ne q uniformLaw hq hqs uniformLaw_pos uniformLaw_sum hne
  rw [divergence_uniformLaw q hqs] at h
  linarith

theorem entropy_continuous : Continuous (entropy : (ι → ℝ) → ℝ) := by
  simp only [show entropy = fun q : ι → ℝ => ∑ i, Real.negMulLog (q i) from
    funext entropy_eq_sum_negMulLog]
  apply continuous_finsetSum
  intro i hi
  exact Real.continuous_negMulLog.comp (continuous_apply i)

theorem primalObjective_continuous (p : ι → ℝ) (c : ℝ) :
    Continuous (primalObjective p c) := by
  change Continuous (fun q : ι → ℝ => divergence q p+max 0 (entropy q-c)/2)
  exact (divergence_continuous p).add
    ((continuous_const.max (entropy_continuous.sub continuous_const)).div_const 2)

/-- Any feasible trial law can be approximated with strictly submaximal full
alphabet entropy. The only endpoint requiring perturbation is the full uniform
law; a small point-mass mixture resolves it without discarding zero atoms of p. -/
theorem primal_trial_approx_strict_entropy (p q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hSupport : ∀ i, 0 < q i → 0 < p i)
    (hD : 2 ≤ Fintype.card ι) (c ε : ℝ) (hε : 0 < ε) :
    ∃ r : ι → ℝ, (∀ i, 0 ≤ r i) ∧ (∑ i, r i = 1) ∧
      (∀ i, 0 < r i → 0 < p i) ∧ entropy r < Real.log (Fintype.card ι) ∧
      primalObjective p c r < primalObjective p c q+ε := by
  by_cases hqu : q = uniformLaw
  · let j : ι := Classical.arbitrary ι
    let d : ι → ℝ := fun i => if i = j then 1 else 0
    have hd : ∀ i, 0 ≤ d i := by intro i; unfold d; split_ifs <;> norm_num
    have hds : ∑ i, d i = 1 := by simp [d]
    have hjp : 0 < p j := hSupport j (by rw [hqu]; exact uniformLaw_pos j)
    have hzero : mixture q d 0 = q := by ext i; simp [mixture]
    have hcont : Continuous (fun t : ℝ => primalObjective p c (mixture q d t)) := by
      apply (primalObjective_continuous p c).comp
      apply continuous_pi
      intro i
      unfold mixture
      fun_prop
    have hevent : ∀ᶠ t : ℝ in 𝓝 0,
        primalObjective p c (mixture q d t) < primalObjective p c q+ε := by
      have hbound : primalObjective p c (mixture q d 0) < primalObjective p c q+ε := by
        rw [hzero]
        linarith
      exact (hcont.continuousAt (x := 0)).eventually (Iio_mem_nhds hbound)
    obtain ⟨δ,hδ,hδall⟩ := Metric.eventually_nhds_iff.mp hevent
    let t := min δ 1/2
    have ht : 0 < t := by dsimp [t]; positivity
    have htδ : t < δ := by have h := min_le_left δ 1; dsimp [t]; linarith
    have ht1 : t < 1 := by have h := min_le_right δ 1; dsimp [t]; linarith
    let r := mixture q d t
    have hr : ∀ i, 0 ≤ r i := mixture_nonneg q d hq hd t ⟨ht.le,ht1.le⟩
    have hrs : ∑ i, r i = 1 := mixture_sum q d hqs hds t
    have hru : r ≠ uniformLaw := by
      intro heq
      have hj := congrFun heq j
      change (1-t)*q j+t*d j = uniformLaw j at hj
      rw [hqu] at hj
      have hDpos : (0:ℝ) < Fintype.card ι := by positivity
      have hDgt : (1:ℝ) < Fintype.card ι := by exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hD
      have huj : uniformLaw (ι := ι) j < 1 := by
        unfold uniformLaw
        rw [inv_eq_one_div]
        rw [div_lt_iff₀ hDpos]
        linarith
      have hdj : d j = 1 := by simp [d]
      rw [hdj] at hj
      nlinarith [mul_pos ht (sub_pos.mpr huj)]
    refine ⟨r,hr,hrs,?_,entropy_lt_log_card_of_ne_uniform r hr hrs hru,?_⟩
    · intro i hi
      by_cases hij : i = j
      · simpa only [hij] using hjp
      · have hdi : d i = 0 := by simp only [d,if_neg hij]
        have hqpos : 0 < q i := by
          change 0 < (1-t)*q i+t*d i at hi
          rw [hdi,mul_zero,add_zero] at hi
          exact (mul_pos_iff_of_pos_left (sub_pos.mpr ht1)).mp hi
        exact hSupport i hqpos
    · exact hδall (by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using htδ)
  · exact ⟨q,hq,hqs,hSupport,entropy_lt_log_card_of_ne_uniform q hq hqs hqu,by linarith⟩

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Full-alphabet entropy endpoints do not obstruct the operational fidelity
exponent: every positive-support variational optimum has arbitrarily close
feasible trials with `H(q)<log D`, including the flat full-rank input. -/
theorem primal_near_minimizer_strict_entropy (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hD : 2 ≤ Fintype.card ι) (c ε : ℝ) (hε : 0 < ε) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∀ i, 0 < q i → 0 < p i) ∧ entropy q < Real.log (Fintype.card ι) ∧
      primalObjective p c q ≤
        (⨅ r : ProbabilityVector (PositiveSupport p), primalObjective (supportLaw p) c r.1)+ε := by
  obtain ⟨α,hα,hopt⟩ := nonnegative_escort_primal_attainment p hp hs c
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα.1
  have hq := escort_nonneg_of_normalized p hp hs α
  have hqs := escort_sum_of_normalized p hp hs α
  have hSupport : ∀ i, 0 < escort p α i → 0 < p i := by
    intro i hi
    by_contra hn
    have hz : p i = 0 := le_antisymm (le_of_not_gt hn) (hp i)
    simp only [escort,hz,Real.zero_rpow (ne_of_gt hαpos),zero_div] at hi
    exact (lt_irrefl 0) hi
  obtain ⟨q,hq,hqs,hSupport,hH,hnear⟩ :=
    primal_trial_approx_strict_entropy p (escort p α) hq hqs hSupport hD c ε hε
  refine ⟨q,hq,hqs,hSupport,hH,?_⟩
  rw [hopt]
  exact hnear.le

end
end ExtractionDeviation
