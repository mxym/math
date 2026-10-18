import SchurCompletion.ScalarTransferAsymptotic

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

def haarOverlapMoment (D s k : ℕ) (hsD : s ≤ D) : ℝ :=
  ∫ U : OneCopyUnitary D, (projectionOverlap D s hsD U/(s : ℝ))^k ∂unitaryHaar D

theorem continuous_projectionOverlap (D s : ℕ) (hsD : s ≤ D) :
    Continuous (projectionOverlap D s hsD) := by unfold projectionOverlap; fun_prop

theorem projectionOverlap_nonneg_le (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    0 ≤ projectionOverlap D s hsD U ∧ projectionOverlap D s hsD U ≤ s := by
  have hG := projectedGram_contraction D s hsD U
  have h0 := (RCLike.nonneg_iff.mp hG.1.trace_nonneg).1
  have h1 := (RCLike.nonneg_iff.mp hG.2.trace_nonneg).1
  change 0 ≤ (projectedGram D s hsD U).trace.re at h0
  change 0 ≤ (1-projectedGram D s hsD U).trace.re at h1
  rw [projectedGram_trace] at h0
  simp only [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Complex.sub_re,
    Complex.natCast_re, projectedGram_trace] at h1
  exact ⟨h0, by linarith⟩

theorem principalMinor_normSq_le_one (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    Complex.normSq (principalMinor D s hsD U).det ≤ 1 := by
  have hG := projectedGram_contraction D s hsD U
  have hd : (projectedGram D s hsD U).det.re =
      ∏ i, hG.1.isHermitian.eigenvalues i := by
    rw [hG.1.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [← projectedGram_det, hd]
  exact Finset.prod_le_one₀ (fun i hi => hG.1.eigenvalues_nonneg i)
    (fun i hi => contraction_eigenvalues_le_one _ hG.1 hG.2 i)

theorem haarMinorMoment_re_integral (D s k : ℕ) (hsD : s ≤ D) :
    (haarMinorMoment D s k hsD).re =
      ∫ U : OneCopyUnitary D, Complex.normSq (principalMinor D s hsD U).det ^ k
        ∂unitaryHaar D := by
  unfold haarMinorMoment
  change RCLike.re (∫ U, minorObservable D s k hsD U ∂unitaryHaar D) = _
  rw [← integral_re ((continuous_minorObservable D s k hsD).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  change (∫ U, (minorObservable D s k hsD U).re ∂unitaryHaar D) = _
  simp only [minorObservable, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem haarOverlapMoment_lower (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (haarMinorMoment D s ⌈(k : ℝ)/(s : ℝ)⌉₊ hsD).re ≤ haarOverlapMoment D s k hsD := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hint (j : ℕ) : Integrable (fun U : OneCopyUnitary D =>
      (projectionOverlap D s hsD U/(s : ℝ))^j) (unitaryHaar D) :=
    (((continuous_projectionOverlap D s hsD).div_const _).pow _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZ (j : ℕ) : Integrable (fun U : OneCopyUnitary D =>
      Complex.normSq (principalMinor D s hsD U).det^j) (unitaryHaar D) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold principalMinor
    fun_prop
  rw [haarMinorMoment_re_integral]
  apply integral_mono (hZ _) (hint _)
  intro U
  have hb := principalMinor_projectionOverlap_bounds D s hs hsD U
  have hY := projectionOverlap_nonneg_le D s hsD U
  have hy0 : 0 ≤ projectionOverlap D s hsD U/(s : ℝ) := div_nonneg hY.1 hsR.le
  have hy1 : projectionOverlap D s hsD U/(s : ℝ) ≤ 1 := (div_le_one hsR).mpr hY.2
  have hp := pow_le_pow_left₀ (Complex.normSq_nonneg _) hb.2 ⌈(k : ℝ)/(s : ℝ)⌉₊
  apply hp.trans
  rw [← pow_mul]
  apply pow_le_pow_of_le_one hy0 hy1
  have hc := Nat.le_ceil ((k : ℝ)/(s : ℝ))
  have hc' := (div_le_iff₀ hsR).mp hc
  exact_mod_cast (by nlinarith : (k : ℝ) ≤ (s : ℝ)*(⌈(k : ℝ)/(s : ℝ)⌉₊ : ℝ))

theorem haarOverlapMoment_upper (D s N k : ℕ) (hs : 0 < s) (hsD : s ≤ D) (hN : 0 < N) :
    haarOverlapMoment D s k hsD ≤
      (haarMinorMoment D s (N*(k/(s*(N+1)))) hsD).re +
        affineStep s (powerCutoff N)^((s*(N+1))*(k/(s*(N+1)))) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hint : Integrable (fun U : OneCopyUnitary D =>
      (projectionOverlap D s hsD U/(s : ℝ))^k) (unitaryHaar D) :=
    (((continuous_projectionOverlap D s hsD).div_const _).pow _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZ : Integrable (fun U : OneCopyUnitary D =>
      Complex.normSq (principalMinor D s hsD U).det^(N*(k/(s*(N+1))))) (unitaryHaar D) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold principalMinor
    fun_prop
  rw [haarMinorMoment_re_integral]
  have hcompare : (∫ U : OneCopyUnitary D,
      (projectionOverlap D s hsD U/(s : ℝ))^k ∂unitaryHaar D) ≤
      ∫ U : OneCopyUnitary D, (Complex.normSq (principalMinor D s hsD U).det^
        (N*(k/(s*(N+1)))) +
        affineStep s (powerCutoff N)^((s*(N+1))*(k/(s*(N+1))))) ∂unitaryHaar D := by
    apply integral_mono hint (hZ.add (integrable_const _))
    intro U
    have hb := principalMinor_projectionOverlap_bounds D s hs hsD U
    have hY := projectionOverlap_nonneg_le D s hsD U
    have hy0 : 0 ≤ projectionOverlap D s hsD U/(s : ℝ) := div_nonneg hY.1 hsR.le
    have hle : projectionOverlap D s hsD U/(s : ℝ) ≤
        affineStep s (Complex.normSq (principalMinor D s hsD U).det) :=
      (div_le_div_iff_of_pos_right hsR).mpr hb.1
    exact (pow_le_pow_left₀ hy0 hle k).trans
      (affineStep_power_global s N k hs hN _ (Complex.normSq_nonneg _)
        (principalMinor_normSq_le_one D s hsD U))
  rw [integral_add hZ (integrable_const _)] at hcompare
  simpa only [integral_const, probReal_univ, one_smul, haarOverlapMoment] using hcompare

end
end ExtractionSchur
