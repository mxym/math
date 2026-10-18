import SchurCompletion.HaarSpectralLower

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem flatHaarAverage_rank_mul_minor_le_one (D s k q : ℕ) (hs : 0 < s) (hsD : s ≤ D)
    (hk : k ≤ s*q) :
    ((flatHaarAverage D s k hsD).rank : ℝ) *
      (((s : ℝ)^k)⁻¹*(haarMinorMoment D s q hsD).re) ≤ 1 := by
  classical
  let Ω := flatHaarAverage D s k hsD
  have hΩ := flatHaarAverage_density D s k hs hsD
  have hpos : Ω.PosSemidef := hΩ.1
  let T : Finset (Word D k) := Finset.univ.filter (fun i => hpos.isHermitian.eigenvalues i ≠ 0)
  have hT : (Ω.rank : ℝ) = (T.card : ℝ) := by
    rw [hpos.isHermitian.rank_eq_card_non_zero_eigs]
    simp only [Fintype.card_subtype, T]
  have htrace : Ω.trace.re = ∑ i, hpos.isHermitian.eigenvalues i := by
    rw [hpos.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have hsum : (∑ i ∈ T, hpos.isHermitian.eigenvalues i) = 1 := by
    have he : (∑ i ∈ T, hpos.isHermitian.eigenvalues i) =
        ∑ i, hpos.isHermitian.eigenvalues i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hnot
    rw [he, ← htrace, hΩ.2, Complex.one_re]
  have hlower (i : Word D k) (hi : i ∈ T) :
      ((s : ℝ)^k)⁻¹*(haarMinorMoment D s q hsD).re ≤ hpos.isHermitian.eigenvalues i := by
    have hne : hpos.isHermitian.eigenvalues i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact flatHaarAverage_positive_eigenvalue_lower D s k q hs hsD hk _
      (lt_of_le_of_ne (hpos.eigenvalues_nonneg i) hne.symm)
      (hpos.isHermitian.eigenvectorBasis i)
      ((WithLp.ofLp_eq_zero 2).ne.2 (hpos.isHermitian.eigenvectorBasis.orthonormal.ne_zero i))
      (hpos.isHermitian.mulVec_eigenvectorBasis i)
  have h := Finset.sum_le_sum hlower
  rw [hsum] at h
  change (Ω.rank : ℝ)*_ ≤ 1
  rw [hT]
  simpa only [Finset.sum_const, nsmul_eq_mul] using h

theorem haarMinorMoment_ceil_scaled_limit (s t : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (k : ℝ)^(s*t)*
      (haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re) atTop
      (𝓝 ((s : ℝ)^(s*t)*weylCrossDenominator s t)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hm : Tendsto (fun k : ℕ => ⌈(k : ℝ)/(s : ℝ)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hsR)
  have h := power_moment_reindex_limit (s*t)
    (fun j => (haarMinorMoment (t+s) s j (by omega)).re) (weylCrossDenominator s t)
    (1/(s : ℝ)) (haarMinorMoment_scaled_limit s t) _ hm (nat_ceil_ratio_limit s hs) (by positivity)
  simpa only [one_div, inv_pow, div_inv_eq_mul, mul_comm] using h

theorem haarMinorMoment_re_pos (s t q : ℕ) :
    0 < (haarMinorMoment (t+s) s q (by omega)).re := by
  rw [haarMinorMoment_product_re]
  apply Finset.prod_pos
  intro i hi
  apply div_pos
  · exact_mod_cast Nat.choose_pos (show q ≤ i+q by omega)
  · exact_mod_cast Nat.choose_pos (show q ≤ t+i+q by omega)

theorem rankBudget_general_rank_upper (s t k : ℕ) (hs : 0 < s) :
    ((rankBudgetProjector (t+s) k s).rank : ℝ) ≤ (s : ℝ)^k /
      (haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hk : k ≤ s*⌈(k : ℝ)/(s : ℝ)⌉₊ := by
    have h := (div_le_iff₀ hsR).mp (Nat.le_ceil ((k : ℝ)/(s : ℝ)))
    exact_mod_cast (by nlinarith : (k : ℝ) ≤ (s : ℝ)*(⌈(k : ℝ)/(s : ℝ)⌉₊ : ℝ))
  have h := flatHaarAverage_rank_mul_minor_le_one (t+s) s k _ hs (by omega) hk
  rw [flatHaarAverage_rank (t+s) s k hs (by omega)] at h
  apply (le_div_iff₀ (haarMinorMoment_re_pos s t _)).mpr
  have hsK : (0 : ℝ) < (s : ℝ)^k := pow_pos hsR _
  have hh := mul_le_mul_of_nonneg_right h hsK.le
  have heq : ((rankBudgetProjector (t+s) k s).rank : ℝ) *
      (((s : ℝ)^k)⁻¹*(haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re) * (s : ℝ)^k =
      ((rankBudgetProjector (t+s) k s).rank : ℝ) *
        (haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re := by
    field_simp
  simpa only [heq, one_mul] using hh

/-- Both sharp actual moments are now proved for every positive rank.
The support upper bound follows from a proved Haar spectral lower bound,
without any Young classification or supplied spectral certificate. -/
theorem rankBudget_general_rank_scaled_limit (s t : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector (t+s) k s).rank : ℝ)/
      ((s : ℝ)^k*(k : ℝ)^(s*t))) atTop (𝓝 (sharpSupportConstant s t)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : 0 < (s : ℝ)^(s*t)*weylCrossDenominator s t :=
    mul_pos (pow_pos hsR _) (weylCrossDenominator_pos s t)
  have hU := (haarMinorMoment_ceil_scaled_limit s t hs).inv₀ hC.ne'
  have he : ((s : ℝ)^(s*t)*weylCrossDenominator s t)⁻¹ = sharpSupportConstant s t := by
    simp [sharpSupportConstant, div_eq_mul_inv, mul_comm]
  rw [he] at hU
  have hup : ∀ᶠ k : ℕ in atTop,
      ((rankBudgetProjector (t+s) k s).rank : ℝ)/((s : ℝ)^k*(k : ℝ)^(s*t)) ≤
      ((k : ℝ)^(s*t)*(haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h := div_le_div_of_nonneg_right (rankBudget_general_rank_upper s t k hs)
      (by positivity : 0 ≤ (s : ℝ)^k*(k : ℝ)^(s*t))
    have hp := haarMinorMoment_re_pos s t ⌈(k : ℝ)/(s : ℝ)⌉₊
    have heq : ((s : ℝ)^k/(haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re) /
        ((s : ℝ)^k*(k : ℝ)^(s*t)) =
        ((k : ℝ)^(s*t)*(haarMinorMoment (t+s) s ⌈(k : ℝ)/(s : ℝ)⌉₊ (by omega)).re)⁻¹ := by
      field_simp
    exact h.trans_eq heq
  apply tendsto_order.2
  constructor
  · intro a ha
    have h := rankBudget_general_sharp_lower s t hs ((sharpSupportConstant s t-a)/2) (by linarith)
    filter_upwards [h] with k hk
    linarith
  · intro a ha
    filter_upwards [hup, (tendsto_order.1 hU).2 a ha] with k hk hl
    exact hk.trans_lt hl

theorem rankBudget_general_rank_isEquivalent (s t : ℕ) (hs : 0 < s) :
    (fun k : ℕ => ((rankBudgetProjector (t+s) k s).rank : ℝ)) ~[atTop]
      (fun k : ℕ => sharpSupportConstant s t*(s : ℝ)^k*(k : ℝ)^(s*t)) := by
  have hC := sharpSupportConstant_pos s t hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : ∀ᶠ k : ℕ in atTop,
      sharpSupportConstant s t*(s : ℝ)^k*(k : ℝ)^(s*t) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  rw [isEquivalent_iff_tendsto_one hn]
  have h := (rankBudget_general_rank_scaled_limit s t hs).div_const (sharpSupportConstant s t)
  rw [div_self hC.ne'] at h
  apply h.congr'
  filter_upwards [] with k
  simp [Pi.div_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The manuscript's actual rank-times-Haar-purity limit, for all ranks. -/
theorem rankBudget_general_rank_times_purity_limit (s t : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector (t+s) k s).rank : ℝ) *
      (flatHaarAverage (t+s) s k (by omega)*flatHaarAverage (t+s) s k (by omega)).trace.re)
      atTop (𝓝 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h := (rankBudget_general_rank_scaled_limit s t hs).mul
    (flatHaarAverage_general_purity_scaled_limit s t hs)
  have he : sharpSupportConstant s t*((s : ℝ)^(s*t)*weylCrossDenominator s t)=1 := by
    unfold sharpSupportConstant
    field_simp [(weylCrossDenominator_pos s t).ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  field_simp

theorem rankBudget_rank_scaled_limit (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector D k s).rank : ℝ)/
      ((s : ℝ)^k*(k : ℝ)^(s*(D-s)))) atTop (𝓝 (sharpSupportConstant s (D-s))) := by
  obtain ⟨t,hD⟩ := Nat.exists_eq_add_of_le hsD
  have hD' : D=t+s := hD.trans (Nat.add_comm s t)
  clear hD
  subst D
  simpa using rankBudget_general_rank_scaled_limit s t hs

theorem rankBudget_rank_times_purity_limit (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    Tendsto (fun k : ℕ => ((rankBudgetProjector D k s).rank : ℝ) *
      (flatHaarAverage D s k hsD*flatHaarAverage D s k hsD).trace.re) atTop (𝓝 1) := by
  obtain ⟨t,hD⟩ := Nat.exists_eq_add_of_le hsD
  have hD' : D=t+s := hD.trans (Nat.add_comm s t)
  clear hD
  subst D
  exact rankBudget_general_rank_times_purity_limit s t hs

end
end ExtractionSchur
