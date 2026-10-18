import SchurCompletion.OverlapAsymptotic

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

theorem projectionOverlap_trace (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    (coordinateRankProjection D s hsD *
      ((U : Matrix (Fin D) (Fin D) ℂ) * coordinateRankProjection D s hsD *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace =
      (projectionOverlap D s hsD U : ℂ) := by
  have he : (projectedGram D s hsD U).trace =
      (coordinateRankProjection D s hsD *
        ((U : Matrix (Fin D) (Fin D) ℂ) * coordinateRankProjection D s hsD *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace := by
    rw [coordinateRankProjection_trace_entries]
    rfl
  have hn := (RCLike.nonneg_iff.mp (projectedGram_contraction D s hsD U).1.trace_nonneg).2
  apply Complex.ext
  · rfl
  · change _ = 0
    rw [← he]
    exact hn

theorem flatHaarAverage_purity_overlap (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (s : ℝ)^k * (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace.re =
      haarOverlapMoment D s k hsD := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have he (U : OneCopyUnitary D) :
      (flatCoordinateDensity D s hsD *
        ((U : Matrix (Fin D) (Fin D) ℂ) * flatCoordinateDensity D s hsD *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace =
        ((projectionOverlap D s hsD U / (s : ℝ)^2 : ℝ) : ℂ) := by
    simp only [flatCoordinateDensity, normalizedProjection, coordinateRankProjection_rank,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast]
    rw [projectionOverlap_trace]
    push_cast
    ring
  have hp : (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace =
      ∫ U : OneCopyUnitary D,
        ((projectionOverlap D s hsD U/(s : ℝ)^2 : ℝ) : ℂ)^k ∂unitaryHaar D := by
    rw [flatHaarAverage, haarOrbitAverage_trace_square]
    simp_rw [he]
  have hci : Integrable (fun U : OneCopyUnitary D =>
      ((projectionOverlap D s hsD U/(s : ℝ)^2 : ℝ) : ℂ)^k) (unitaryHaar D) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (Complex.continuous_ofReal.comp ((continuous_projectionOverlap D s hsD).div_const _)).pow _
  rw [hp]
  change (s : ℝ)^k * RCLike.re (∫ U : OneCopyUnitary D,
    ((projectionOverlap D s hsD U/(s : ℝ)^2 : ℝ) : ℂ)^k ∂unitaryHaar D) = _
  rw [← integral_re hci]
  change (s : ℝ)^k * (∫ U : OneCopyUnitary D,
    (((projectionOverlap D s hsD U/(s : ℝ)^2 : ℝ) : ℂ)^k).re ∂unitaryHaar D) = _
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [div_pow, div_pow, pow_right_comm (s : ℝ) 2 k]
  field_simp
  <;> ring

/-- Sharp actual Haar purity for every positive rank s in dimension t+s.
Its sole numerical data are the dimension and rank; no Young decomposition,
spectral certificate, or concentration statement is supplied as a premise. -/
theorem flatHaarAverage_general_purity_scaled_limit (s t : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (s : ℝ)^k * (k : ℝ)^(s*t) *
      (flatHaarAverage (t+s) s k (by omega) * flatHaarAverage (t+s) s k (by omega)).trace.re)
      atTop (𝓝 ((s : ℝ)^(s*t)*weylCrossDenominator s t)) := by
  have h := haarOverlapMoment_scaled_limit s t hs
  apply h.congr'
  filter_upwards [] with k
  rw [← flatHaarAverage_purity_overlap (t+s) s k hs (by omega)]
  ring

theorem flatHaarAverage_general_purity_isEquivalent (s t : ℕ) (hs : 0 < s) :
    (fun k : ℕ => (flatHaarAverage (t+s) s k (by omega) *
      flatHaarAverage (t+s) s k (by omega)).trace.re) ~[atTop]
      (fun k : ℕ => ((s : ℝ)^(s*t)*weylCrossDenominator s t) /
        ((s : ℝ)^k*(k : ℝ)^(s*t))) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : 0 < (s : ℝ)^(s*t)*weylCrossDenominator s t :=
    mul_pos (pow_pos hsR _) (weylCrossDenominator_pos s t)
  have hn : ∀ᶠ k : ℕ in atTop,
      ((s : ℝ)^(s*t)*weylCrossDenominator s t) / ((s : ℝ)^k*(k : ℝ)^(s*t)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  rw [isEquivalent_iff_tendsto_one hn]
  have h := (flatHaarAverage_general_purity_scaled_limit s t hs).div_const
    ((s : ℝ)^(s*t)*weylCrossDenominator s t)
  rw [div_self hC.ne'] at h
  apply h.congr'
  filter_upwards [] with k
  simp [Pi.div_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem flatHaarAverage_purity_scaled_limit (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    Tendsto (fun k : ℕ => (s : ℝ)^k * (k : ℝ)^(s*(D-s)) *
      (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace.re)
      atTop (𝓝 ((s : ℝ)^(s*(D-s))*weylCrossDenominator s (D-s))) := by
  obtain ⟨t, hD⟩ := Nat.exists_eq_add_of_le hsD
  have hD' : D = t+s := hD.trans (Nat.add_comm s t)
  clear hD
  subst D
  simpa using
    flatHaarAverage_general_purity_scaled_limit s t hs

/-- The sharp leading lower bound for the actual support rank, now for every
positive rank. The matching upper bound remains a separate theorem. -/
theorem rankBudget_general_sharp_lower (s t : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, sharpSupportConstant s t - ε ≤
      ((rankBudgetProjector (t+s) k s).rank : ℝ) / ((s : ℝ)^k*(k : ℝ)^(s*t)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : 0 < (s : ℝ)^(s*t)*weylCrossDenominator s t :=
    mul_pos (pow_pos hsR _) (weylCrossDenominator_pos s t)
  have hlim := (flatHaarAverage_general_purity_scaled_limit s t hs).inv₀ hC.ne'
  have he : ((s : ℝ)^(s*t)*weylCrossDenominator s t)⁻¹ = sharpSupportConstant s t := by
    simp [sharpSupportConstant, mul_inv, div_eq_mul_inv, mul_comm]
  rw [he] at hlim
  have hlower := (tendsto_order.1 hlim).1 (sharpSupportConstant s t-ε) (by linarith)
  filter_upwards [hlower, eventually_ge_atTop 1] with k hk hk1
  apply le_trans hk.le
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  let scale : ℝ := (s : ℝ)^k*(k : ℝ)^(s*t)
  have hscale : 0 < scale := mul_pos (pow_pos hsR _) (pow_pos hkR _)
  let p := (flatHaarAverage (t+s) s k (by omega) * flatHaarAverage (t+s) s k (by omega)).trace.re
  have hRP : 1 ≤ ((rankBudgetProjector (t+s) k s).rank : ℝ)*p := by
    have h := haarOrbitAverage_rank_times_purity_ge_one (t+s) k
      (flatCoordinateDensity (t+s) s (by omega))
      (flatCoordinateDensity_density (t+s) s hs (by omega))
    simpa only [flatCoordinateDensity_rank (t+s) s hs (by omega), p, flatHaarAverage] using h
  have hp : 0 < p := by
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℝ) ≤ (rankBudgetProjector (t+s) k s).rank by positivity) (le_of_not_gt hn)
    linarith
  change (scale*p)⁻¹ ≤ ((rankBudgetProjector (t+s) k s).rank : ℝ)/scale
  rw [← one_div, div_le_div_iff₀ (mul_pos hscale hp) hscale]
  have h := mul_le_mul_of_nonneg_left hRP hscale.le
  nlinarith

end
end ExtractionSchur
