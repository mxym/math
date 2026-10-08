import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
open scoped NumberField nonZeroDivisors Multiplicative
open NumberField IsDedekindDomain
namespace Entry002

/-- An actual normalized discrete valuation bounds every maximal-ideal power. -/
theorem arithmeticSupply_valuation_maximal_pow_bound {L : Type*} [Field L]
    (w : Valuation L (WithZero (Multiplicative ℤ))) [w.IsRankOneDiscrete]
    (hrange : WithZero.exp (-1 : ℤ) ∈ Set.range w) (n : ℕ)
    (a : w.valuationSubring)
    (ha : a ∈ IsLocalRing.maximalIdeal w.valuationSubring ^ n) :
    w (a : L) ≤ WithZero.exp (-(n : ℤ)) := by
  let π : w.Uniformizer := Classical.choice inferInstance
  have hg := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range hrange
  have hπ : w (π.val : L) = WithZero.exp (-1 : ℤ) := by
    rw [Valuation.IsUniformizer.val π.valuation_gt_one, hg]
    rfl
  rw [Valuation.pow_Uniformizer_is_pow_generator π n, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  change w (a : L) ≤ _
  rw [hb, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, hπ]
  calc
    _ ≤ WithZero.exp (-1 : ℤ) ^ n * 1 := mul_le_mul_of_nonneg_left b.property zero_le
    _ = WithZero.exp (-(n : ℤ)) := by simp [← WithZero.exp_nsmul]

/-- A completion congruence gives its actual normalized valuation bound. -/
theorem arithmeticSupply_completed_pow_valuation_bound
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : v.adicCompletionIntegers K)
    (ha : a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    Valued.v (a : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  apply arithmeticSupply_valuation_maximal_pow_bound
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) _ n a ha
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer K
  refine ⟨(r : v.adicCompletion K), ?_⟩
  simpa [v.valuedAdicCompletion_eq_valuation'] using hr

/-- Prime-power congruences reflect from the completion to the global integers. -/
theorem arithmeticSupply_completed_pow_reflects
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : 𝓞 K)
    (ha : algebraMap (𝓞 K) (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :
    a ∈ v.asIdeal ^ n := by
  apply (v.intValuation_le_pow_iff_mem a n).mp
  have h := arithmeticSupply_completed_pow_valuation_bound K v n _ ha
  change Valued.v ((a : K) : v.adicCompletion K) ≤ _ at h
  rwa [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap] at h

/-- Actual valuation divisibility at every finite place gives actual global divisibility. -/
theorem arithmeticSupply_dvd_of_local_valuation_bounds
    (K : Type*) [Field K] [NumberField K] (d a : 𝓞 K) (hd : d ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K (a : K) ≤ v.valuation K (d : K)) : d ∣ a := by
  have hdK : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hq : ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K ((a : K) / (d : K)) ≤ 1 := by
    intro v
    rw [map_div₀]
    exact (div_le_one₀ ((Valuation.pos_iff _).mpr hdK)).mpr (h v)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
    K ((a : K) / (d : K)) hq
  refine ⟨b, RingOfIntegers.coe_injective ?_⟩
  change (a : K) = (d : K) * (b : K)
  change (b : K) = (a : K) / (d : K) at hb
  rw [hb]
  exact (mul_div_cancel₀ (a : K) hdK).symm

end Entry002
