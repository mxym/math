import SchurCompletion.HaarOrbit

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem continuous_orbit_traceLeft (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Word D k) (Word D k) ℂ) :
    Continuous (fun U => (A * orbitTensor D k X U).trace) :=
  (traceLeftLinear A).continuous_of_finiteDimensional.comp (continuous_orbitTensor D k X)

/-- A nonnegative continuous deficit with Haar integral zero vanishes on the
entire actual orbit. No strict-positivity certificate is supplied. -/
theorem exact_haar_average_iff_exact_orbit (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1-M).PosSemidef) :
    (M * haarOrbitAverage D k X).trace.re = 1 ↔
      ∀ U : OneCopyUnitary D, (M * orbitTensor D k X U).trace.re = 1 := by
  have hOrbit (U : OneCopyUnitary D) :
      (orbitTensor D k X U).PosSemidef ∧ (orbitTensor D k X U).trace = 1 :=
    tensorMatrix_density _ (fixed_density_unitary_conjugate_density D X hX U) k
  let f : OneCopyUnitary D → ℝ := fun U => ((1-M) * orbitTensor D k X U).trace.re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_orbit_traceLeft D k X (1-M))
  have hfi : Integrable f (unitaryHaar D) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg (U) : 0 ≤ f U :=
    Extraction.positive_product_trace_re _ _ hM (hOrbit U).1
  constructor
  · intro hfit
    have hz : ∫ U, f U ∂unitaryHaar D = 0 := by
      rw [show (fun U => f U) = (fun U => ((1-M) * orbitTensor D k X U).trace.re) from rfl]
      change (∫ U, RCLike.re (((1-M) * orbitTensor D k X U).trace) ∂unitaryHaar D) = 0
      rw [integral_re ((continuous_orbit_traceLeft D k X (1-M)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)), ← haarOrbitAverage_traceLeft]
      change ((1-M) * haarOrbitAverage D k X).trace.re = 0
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
        (haarOrbitAverage_density D k X hX).2, Complex.one_re, hfit, sub_self]
    have hae : f =ᵐ[unitaryHaar D] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg hfi).mp hz
    have hpoint : f = 0 := (hf.ae_eq_iff_eq (unitaryHaar D) continuous_zero).mp hae
    intro U
    have h := congrFun hpoint U
    change ((1-M) * orbitTensor D k X U).trace.re = 0 at h
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
      (hOrbit U).2, Complex.one_re] at h
    linarith
  · intro hfit
    have h := haarOrbitAverage_traceLeft D k X M
    have hInt := (continuous_orbit_traceLeft D k X M).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := unitaryHaar D)
    rw [h]
    change RCLike.re (∫ U, (M * orbitTensor D k X U).trace ∂unitaryHaar D) = 1
    rw [← integral_re hInt]
    change (∫ U, (M * orbitTensor D k X U).trace.re ∂unitaryHaar D) = 1
    simp only [hfit, integral_const, probReal_univ, one_smul]

theorem exact_haar_average_effect_mul_support (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1-M).PosSemidef)
    (hfit : (M * haarOrbitAverage D k X).trace.re = 1) :
    M * rankBudgetProjector D k X.rank = rankBudgetProjector D k X.rank :=
  exact_fixed_density_orbit_effect_mul_rankBudgetProjector D k X hX M hM
    ((exact_haar_average_iff_exact_orbit D k X hX M hM).mp hfit)

/-- The literal Haar average has exactly the intrinsic minimal rank-budget
support, for every blocklength including zero and every actual fixed density. -/
theorem haarOrbitAverage_range (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    LinearMap.range (haarOrbitAverage D k X).mulVecLin = rankBudgetSpace D k X.rank := by
  classical
  let Ω := haarOrbitAverage D k X
  obtain ⟨Q, hQ, hQQ, hQR, hQRank, hQfix⟩ :=
    MatrixSubspace.exists_subspace_projection (LinearMap.range Ω.mulVecLin)
  have hQΩ : Q * Ω = Ω := by
    apply matrix_mul_eq_of_fixes_columns
    intro w
    apply hQfix
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w, rfl⟩
  have hcomp : (1-Q).PosSemidef := by
    have hh := Matrix.posSemidef_self_mul_conjTranspose (1-Q)
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ.eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ,
      sub_sub_cancel, sub_self, sub_zero] using hh
  have hQP : Q * rankBudgetProjector D k X.rank = rankBudgetProjector D k X.rank := by
    apply exact_haar_average_effect_mul_support D k X hX Q hcomp
    rw [show haarOrbitAverage D k X = Ω from rfl, hQΩ, (haarOrbitAverage_density D k X hX).2]
    rfl
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    rw [← rankBudgetProjector_range]
    refine ⟨Ω *ᵥ x, ?_⟩
    change rankBudgetProjector D k X.rank *ᵥ (Ω *ᵥ x) = Ω *ᵥ x
    rw [Matrix.mulVec_mulVec, haarOrbitAverage_common_support]
  · intro v hv
    rw [← hQR]
    refine ⟨v, ?_⟩
    change Q *ᵥ v = v
    rw [← rankBudgetProjector_fixes D k X.rank v hv]
    rw [Matrix.mulVec_mulVec, hQP]

theorem haarOrbitAverage_rank (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    (haarOrbitAverage D k X).rank = (rankBudgetProjector D k X.rank).rank := by
  change Module.finrank ℂ (LinearMap.range (haarOrbitAverage D k X).mulVecLin) = _
  rw [haarOrbitAverage_range D k X hX, rankBudgetProjector_rank]

/-- The manuscript's actual flat-support adversarial average. -/
def flatHaarAverage (D s k : ℕ) (hsD : s ≤ D) : Matrix (Word D k) (Word D k) ℂ :=
  haarOrbitAverage D k (flatCoordinateDensity D s hsD)

theorem flatHaarAverage_density (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (flatHaarAverage D s k hsD).PosSemidef ∧ (flatHaarAverage D s k hsD).trace = 1 :=
  haarOrbitAverage_density D k _ (flatCoordinateDensity_density D s hs hsD)

theorem flatHaarAverage_range (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    LinearMap.range (flatHaarAverage D s k hsD).mulVecLin = rankBudgetSpace D k s := by
  simpa only [flatHaarAverage, flatCoordinateDensity_rank D s hs hsD] using
    haarOrbitAverage_range D k _ (flatCoordinateDensity_density D s hs hsD)

theorem flatHaarAverage_rank (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (flatHaarAverage D s k hsD).rank = (rankBudgetProjector D k s).rank := by
  simpa only [flatHaarAverage, flatCoordinateDensity_rank D s hs hsD] using
    haarOrbitAverage_rank D k _ (flatCoordinateDensity_density D s hs hsD)

end
end ExtractionSchur
