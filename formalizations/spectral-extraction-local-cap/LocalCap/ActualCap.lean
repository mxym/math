import LocalCap.SchmidtBudget

open scoped BigOperators ComplexOrder
open Matrix
namespace ExtractionLocalCap

variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

/-- Actual partial-transpose two-sided order control implies the local-dimension
operator cap. The proof tests all original complex vectors and obtains their
Schmidt models internally. -/
theorem local_order_cap (M : Matrix (a × b) (a × b) ℂ)
    (hM : M.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (hlo : (c • (1 : Matrix (a × b) (a × b) ℂ) +
      APPT.Quantum.partialTranspose M).PosSemidef)
    (hhi : (c • (1 : Matrix (a × b) (a × b) ℂ) -
      APPT.Quantum.partialTranspose M).PosSemidef) :
    ((c * Fintype.card a) • (1 : Matrix (a × b) (a × b) ℂ) - M).PosSemidef := by
  have hH : ((c * Fintype.card a) • (1 : Matrix (a × b) (a × b) ℂ) - M).IsHermitian := by
    change ((c * Fintype.card a) • (1 : Matrix (a × b) (a × b) ℂ) - M)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, hM.eq]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro w
  have h := pure_partialTranspose_pairing_le (APPT.Quantum.partialTranspose M)
    c hc hlo hhi w
  have he : (APPT.Quantum.partialTranspose M *
      APPT.Quantum.partialTranspose (Matrix.vecMulVec w (star w))).trace =
      (M * Matrix.vecMulVec w (star w)).trace := by
    simpa only [APPT.Quantum.partialTranspose_involutive] using
      (Extraction.trace_partialTranspose_pairing M
        (APPT.Quantum.partialTranspose (Matrix.vecMulVec w (star w)))).symm
  rw [he, Extraction.trace_mul_pure] at h
  have hr :
      0 ≤ (star w ⬝ᵥ
        (((c * Fintype.card a) • (1 : Matrix (a × b) (a × b) ℂ) - M) *ᵥ w)).re := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, Complex.sub_re, Complex.smul_re,
      smul_eq_mul] using sub_nonneg.mpr h
  exact RCLike.nonneg_iff.mpr ⟨hr, hH.im_star_dotProduct_mulVec_self w⟩

/-- The Rains conditions imply a/K as a real PSD matrix inequality. -/
theorem rainsEffect_local_order_cap (K : ℕ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : Extraction.RainsEffect K M) :
    (((Fintype.card a : ℝ) / K) • (1 : Matrix (a × b) (a × b) ℂ) - M).PosSemidef := by
  have h := local_order_cap M hM.1.isHermitian (1 / (K : ℝ))
    (by positivity) hM.2.2.1 hM.2.2.2
  have he : (1 / (K : ℝ)) * Fintype.card a = (Fintype.card a : ℝ) / K := by ring
  rw [he] at h
  exact h

/-- The local cap is transferred to every actual trace-one PSD density. -/
theorem rainsEffect_density_overlap_le (K : ℕ)
    (M X : Matrix (a × b) (a × b) ℂ) (hM : Extraction.RainsEffect K M)
    (hX : APPT.Quantum.IsDensity X) :
    (M * X).trace.re ≤ (Fintype.card a : ℝ) / K := by
  have h := Extraction.positive_product_trace_re X
    (((Fintype.card a : ℝ) / K) • (1 : Matrix (a × b) (a × b) ℂ) - M)
    hX.1 (rainsEffect_local_order_cap K M hM)
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, Complex.sub_re, Complex.smul_re, hX.2,
    Complex.one_re, smul_eq_mul, mul_one] at h
  rw [Matrix.trace_mul_comm M X]
  linarith

variable {d κ : Type*} [Fintype d] [Fintype κ] [DecidableEq d] [Nonempty d]

/-- A physical trace-preserving Kraus channel with positive transpose conjugate
has output overlap at most a/K, without an effect-level cap assumption. -/
theorem kraus_target_overlap_local_cap
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X) :
    (Extraction.bellProjector (d := d) * Extraction.krausApply A X).trace.re ≤
      (Fintype.card a : ℝ) / Fintype.card d := by
  rw [Extraction.target_overlap_eq]
  exact rainsEffect_density_overlap_le _ _ X
    (Extraction.targetEffect_rains A hcomplete hpt) hX

/-- The physical a/K bound is uniform over every initial global unitary. -/
theorem kraus_target_overlap_unitary_local_cap
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    (Extraction.bellProjector (d := d) *
      Extraction.krausApply A ((U : Matrix (a × b) (a × b) ℂ) * X *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re ≤
      (Fintype.card a : ℝ) / Fintype.card d := by
  have hU : (U : Matrix (a × b) (a × b) ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  exact kraus_target_overlap_local_cap A hcomplete hpt _ ⟨hX.1.mul_mul_conjTranspose_same _,
    (Extraction.isometry_trace_congruence _ hU X).trans hX.2⟩

/-- The complete finite one-shot envelope for actual channels and all-unitary
preprocessing: unit, local dimension, and purity bounds hold simultaneously. -/
theorem kraus_target_overlap_full_envelope
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    (Extraction.bellProjector (d := d) *
      Extraction.krausApply A ((U : Matrix (a × b) (a × b) ℂ) * X *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re ≤
      min 1 (min ((Fintype.card a : ℝ) / Fintype.card d)
        (Real.sqrt ((X * X).trace.re *
          ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2)))) := by
  have hU : (U : Matrix (a × b) (a × b) ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hstate : APPT.Quantum.IsDensity
      ((U : Matrix (a × b) (a × b) ℂ) * X *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ) :=
    ⟨hX.1.mul_mul_conjTranspose_same _,
      (Extraction.isometry_trace_congruence _ hU X).trans hX.2⟩
  exact le_min (Extraction.kraus_target_overlap_le_one A hcomplete hpt _ hstate)
    (le_min (kraus_target_overlap_unitary_local_cap A hcomplete hpt X hX U)
      (Extraction.kraus_target_overlap_unitary_le A hcomplete hpt X hX.1.isHermitian U))

end ExtractionLocalCap
