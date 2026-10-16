import SpectralProtocol.PureBell

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive effect perfect on all positive matrices in a subspace fixes that
subspace, without requiring commutation with a later input density. -/
theorem effect_fixes_projection_of_exact_support
    (M P : Matrix ι ι ℂ) (hQ : (1-M).PosSemidef)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hexact : ∀ Y : Matrix ι ι ℂ, Y.PosSemidef → P*Y*P=Y →
      (M*Y).trace.re=Y.trace.re) : M*P=P := by
  have hfix (v : ι → ℂ) : M.mulVec (P.mulVec v)=P.mulVec v := by
    let w := P.mulVec v
    let Y := Matrix.vecMulVec w (star w)
    have hw : P.mulVec w=w := by
      change P.mulVec (P.mulVec v)=P.mulVec v
      rw [Matrix.mulVec_mulVec,hPP]
    have hYP : P*Y*P=Y := by
      have h := Extraction.congruence_pure P w
      simpa only [hP.eq,hw] using h
    have hYpos : Y.PosSemidef := Matrix.posSemidef_vecMulVec_self_star w
    have he := hexact Y hYpos hYP
    have hreal : (star w ⬝ᵥ (1-M).mulVec w).re=0 := by
      rw [← Extraction.trace_mul_pure]
      change ((1-M)*Y).trace.re=0
      simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re]
      linarith
    have hzero : star w ⬝ᵥ (1-M).mulVec w=0 := by
      apply Complex.ext hreal
      exact hQ.isHermitian.im_star_dotProduct_mulVec_self w
    have hnull := hQ.dotProduct_mulVec_zero_iff.mp hzero
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero] at hnull
    exact hnull.symm
  ext i j
  have hj := congrArg (fun v => v i) (hfix (Pi.single j 1))
  rw [Matrix.mulVec_mulVec] at hj
  simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col,Matrix.transpose_apply] using hj

/-- An actual positive effect that fixes P dominates P as a PSD matrix. -/
theorem effect_sub_projection_posSemidef (M P : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hP : P.IsHermitian) (hPP : P*P=P)
    (hMP : M*P=P) : (M-P).PosSemidef := by
  have hPM : P*M=P := by
    have h := congrArg Matrix.conjTranspose hMP
    simpa only [Matrix.conjTranspose_mul,hM.isHermitian.eq,hP.eq] using h
  have h := hM.mul_mul_conjTranspose_same (1-P)
  have hPH : (1-P)ᴴ=1-P := by simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.eq]
  have he : (1-P)*M*(1-P)=M-P := by
    simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,hPM,hMP,hPP]
    abel
  rwa [hPH,he] at h

/-- The common-subspace packing lower bound applies to the total support mass
of an arbitrary actual density, including off-diagonal support-complement
coherences. No commutation or positive-remainder premise is needed. -/
theorem finite_projection_mass_lower (a b K : ℕ) (hK : 0 < K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hr : P.rank ≤ (a/K)*(b/K)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a/K) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/K) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, X.PosSemidef →
        (P*X).trace.re ≤
          (Extraction.bellProjector (d := Fin K) *
            Extraction.krausApply (Extraction.productKraus A B)
              ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)*X*
                (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  obtain ⟨U,A,B,hA,hB,he⟩ := Extraction.finite_projection_exact_extractor a b K hK P hP hPP hr
  let C := Extraction.productKraus A B
  have hC : ∑ j,(C j)ᴴ*C j=1 := Extraction.productKraus_complete A B hA hB
  have hpt := productKraus_PTConjugatePositive A B
  let M := preprocessedEffect C U
  have hM : M.PosSemidef := by
    simpa only [M, preprocessedEffect,Matrix.conjTranspose_conjTranspose] using
      (Extraction.targetEffect_rains C hC hpt).1.mul_mul_conjTranspose_same
        (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ
  have hMP : M*P=P := effect_fixes_projection_of_exact_support M P
    (one_sub_preprocessedEffect_posSemidef C hC hpt U) hP hPP (by
      intro Y hY hPY
      rw [← preprocessedEffect_pairing,he Y hPY]
      simp only [Matrix.mul_smul,Extraction.bellProjector_idempotent,Matrix.trace_smul,smul_eq_mul]
      have hbt : (Extraction.bellProjector (d := Fin K)).trace=1 := (Extraction.bellProjector_density (d := Fin K)).2
      rw [hbt,mul_one])
  refine ⟨U,A,B,hA,hB,?_⟩
  intro X hX
  rw [preprocessedEffect_pairing]
  have h := Extraction.positive_product_trace_re (M-P) X
    (effect_sub_projection_posSemidef M P hM hP hPP hMP) hX
  simp only [Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re] at h
  change (P*X).trace.re ≤ (M*X).trace.re
  linarith

end SpectralProtocol