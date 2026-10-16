import CircuitCompletion.OperatorError

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitCompletion

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [Nonempty d]

/-- Actual complete finite PPT postprocessing retains fidelity at least
1-2δ when the sole original-space unitary is approximated in Euclidean
operator norm. No channel-contraction hypothesis is supplied. -/
theorem physical_fidelity_robust
    (A : κ → Matrix (d×d) (a×b) ℂ) (hcomplete : ∑ j,(A j)ᴴ*A j=1)
    (hpt : Extraction.PTConjugatePositive A)
    (U V : Matrix.unitaryGroup (a×b) ℂ) (z : a×b → ℂ) (hz : vectorSquare z=1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hUV : ‖(U : Matrix (a×b) (a×b) ℂ)-(V : Matrix (a×b) (a×b) ℂ)‖ ≤ δ)
    (hexact : (Extraction.bellProjector (d := d)*Extraction.krausApply A
      ((U : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(U : Matrix (a×b) (a×b) ℂ)ᴴ)).trace.re=1) :
    1-2*δ ≤ (Extraction.bellProjector (d := d)*Extraction.krausApply A
      ((V : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(V : Matrix (a×b) (a×b) ℂ)ᴴ)).trace.re := by
  have hpre (W : Matrix.unitaryGroup (a×b) ℂ) :
      (Extraction.targetEffect A*pureMatrix ((W : Matrix (a×b) (a×b) ℂ)*ᵥz)).trace.re=
        (Extraction.bellProjector (d := d)*Extraction.krausApply A
          ((W : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(W : Matrix (a×b) (a×b) ℂ)ᴴ)).trace.re := by
    symm
    rw [Extraction.target_overlap_eq]
    have hc : (W : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(W : Matrix (a×b) (a×b) ℂ)ᴴ=
        pureMatrix ((W : Matrix (a×b) (a×b) ℂ)*ᵥz) := Extraction.congruence_pure _ _
    rw [hc]
  rw [← hpre V]
  have hb := Extraction.targetEffect_rains A hcomplete hpt
  apply exact_effect_fidelity_lower_delta _ hb.1 hb.2.1 _ _
    ((vectorSquare_unitary U z).trans hz) ((vectorSquare_unitary V z).trans hz)
    ((hpre U).trans hexact) δ hδ
  exact operator_error_controls_vector U V z hz δ hδ hUV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def phaseUnitary (c : ℂ) (hc : Complex.normSq c=1)
    (V : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup ι ℂ := by
  have hs : c*star c=1 := by
    simpa only [starRingEnd_apply,Complex.ofReal_one] using (Complex.mul_conj c).trans (congrArg Complex.ofReal hc)
  have hcs : star c*c=1 := by rw [mul_comm];exact hs
  refine ⟨c • (V : Matrix ι ι ℂ),Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (c • (V : Matrix ι ι ℂ))ᴴ*(c • (V : Matrix ι ι ℂ))=1
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hs,hcs,
    one_smul]
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V

theorem phaseUnitary_congruence (c : ℂ) (hc : Complex.normSq c=1)
    (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    (phaseUnitary c hc V : Matrix ι ι ℂ)*X*(phaseUnitary c hc V : Matrix ι ι ℂ)ᴴ=
      (V : Matrix ι ι ℂ)*X*(V : Matrix ι ι ℂ)ᴴ := by
  have hs : c*star c=1 := by
    simpa only [starRingEnd_apply,Complex.ofReal_one] using (Complex.mul_conj c).trans (congrArg Complex.ofReal hc)
  have hcs : star c*c=1 := by rw [mul_comm];exact hs
  change (c • (V : Matrix ι ι ℂ))*X*(c • (V : Matrix ι ι ℂ))ᴴ=_
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hs,hcs,one_smul]

/-- The irrelevant overall phase in a finite-library compiler is removed
inside the actual matrix/channel proof, not assumed to be physically supplied. -/
theorem physical_fidelity_robust_up_to_phase
    (A : κ → Matrix (d×d) (a×b) ℂ) (hcomplete : ∑ j,(A j)ᴴ*A j=1)
    (hpt : Extraction.PTConjugatePositive A)
    (U V : Matrix.unitaryGroup (a×b) ℂ) (z : a×b → ℂ) (hz : vectorSquare z=1)
    (δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (hc : Complex.normSq c=1)
    (hUV : ‖(U : Matrix (a×b) (a×b) ℂ)-c • (V : Matrix (a×b) (a×b) ℂ)‖ ≤ δ)
    (hexact : (Extraction.bellProjector (d := d)*Extraction.krausApply A
      ((U : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(U : Matrix (a×b) (a×b) ℂ)ᴴ)).trace.re=1) :
    1-2*δ ≤ (Extraction.bellProjector (d := d)*Extraction.krausApply A
      ((V : Matrix (a×b) (a×b) ℂ)*pureMatrix z*(V : Matrix (a×b) (a×b) ℂ)ᴴ)).trace.re := by
  have h := physical_fidelity_robust A hcomplete hpt U (phaseUnitary c hc V) z hz δ hδ hUV hexact
  rwa [phaseUnitary_congruence] at h

end CircuitCompletion
