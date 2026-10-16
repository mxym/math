import SpectralProtocol.MultisectorMass
import SpectralProtocol.BellTensor

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι ο τ σ : Type*} [Fintype ι] [Fintype ο] [Fintype τ] [Fintype σ]
  [DecidableEq ι] [DecidableEq ο]

noncomputable def halfAmplitude : ℂ := (Real.sqrt (1/2:ℝ) : ℂ)

theorem halfAmplitude_square : halfAmplitude*halfAmplitude=(1/2:ℂ) := by
  unfold halfAmplitude
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem halfAmplitude_star : star halfAmplitude=halfAmplitude := by
  exact Complex.conj_ofReal _

def unionKraus (A : τ → Matrix ο ι ℂ) (B : σ → Matrix ο ι ℂ) :
    τ⊕σ → Matrix ο ι ℂ := Sum.elim A B

noncomputable def halfMixKraus (A : τ → Matrix ο ι ℂ) (B : σ → Matrix ο ι ℂ) :
    τ⊕σ → Matrix ο ι ℂ := fun j => halfAmplitude • unionKraus A B j

theorem halfMixKraus_complete (A : τ → Matrix ο ι ℂ) (B : σ → Matrix ο ι ℂ)
    (hA : ∑ j,(A j)ᴴ*A j=1) (hB : ∑ j,(B j)ᴴ*B j=1) :
    ∑ j,(halfMixKraus A B j)ᴴ*halfMixKraus A B j=1 := by
  simp only [halfMixKraus,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    halfAmplitude_star,smul_smul,halfAmplitude_square,← Finset.smul_sum,
    Fintype.sum_sum_type,unionKraus,Sum.elim_inl,Sum.elim_inr,hA,hB]
  ext i j
  by_cases hij : i=j
  · subst j
    change (1/2:ℂ)*((1 : Matrix ι ι ℂ) i i+(1 : Matrix ι ι ℂ) i i)=(1 : Matrix ι ι ℂ) i i
    norm_num [Matrix.one_apply]
  · simp [Matrix.one_apply,hij]

theorem krausApply_scaled (c : ℂ) (A : τ → Matrix ο ι ℂ) (X : Matrix ι ι ℂ) :
    Extraction.krausApply (fun j => c • A j) X=
      (c*star c) • Extraction.krausApply A X := by
  simp only [Extraction.krausApply,Matrix.conjTranspose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,← Finset.smul_sum]
  rw [mul_comm c (star c)]

variable {α β π υ ω : Type*} [Fintype α] [Fintype β] [Fintype π]
  [Fintype υ] [Fintype ω] [DecidableEq α] [DecidableEq β] [DecidableEq π]

theorem product_unionKraus_apply
    (A : τ → Matrix ο ι ℂ) (C : σ → Matrix ο ι ℂ)
    (B : υ → Matrix π α ℂ) (D : ω → Matrix π α ℂ)
    (X : Matrix (ι×α) (ι×α) ℂ) :
    Extraction.krausApply (Extraction.productKraus (unionKraus A C) (unionKraus B D)) X=
      Extraction.krausApply (Extraction.productKraus A B) X+
      Extraction.krausApply (Extraction.productKraus A D) X+
      Extraction.krausApply (Extraction.productKraus C B) X+
      Extraction.krausApply (Extraction.productKraus C D) X := by
  simp only [Extraction.krausApply,Fintype.sum_prod_type,Fintype.sum_sum_type,
    Extraction.productKraus,unionKraus,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib]
  abel

theorem product_halfMixKraus_apply
    (A : τ → Matrix ο ι ℂ) (C : σ → Matrix ο ι ℂ)
    (B : υ → Matrix π α ℂ) (D : ω → Matrix π α ℂ)
    (X : Matrix (ι×α) (ι×α) ℂ) :
    Extraction.krausApply (Extraction.productKraus (halfMixKraus A C) (halfMixKraus B D)) X=
      (1/4:ℂ) • (Extraction.krausApply (Extraction.productKraus A B) X+
      Extraction.krausApply (Extraction.productKraus A D) X+
      Extraction.krausApply (Extraction.productKraus C B) X+
      Extraction.krausApply (Extraction.productKraus C D) X) := by
  have hp : Extraction.productKraus (halfMixKraus A C) (halfMixKraus B D)=
      fun j => (1/2:ℂ) • Extraction.productKraus (unionKraus A C) (unionKraus B D) j := by
    funext j
    simp only [Extraction.productKraus,halfMixKraus,Matrix.smul_kronecker,
      Matrix.kronecker_smul,smul_smul,halfAmplitude_square]
  rw [hp,krausApply_scaled,product_unionKraus_apply]
  norm_num

/-- A deterministic local reset is a complete actual finite Kraus channel. -/
def resetKraus (o₀ : ο) : ι → Matrix ο ι ℂ :=
  Extraction.residualKraus o₀ (1 : Matrix ι ι ℂ)

theorem resetKraus_complete (o₀ : ο) : ∑ j,(resetKraus (ι := ι) o₀ j)ᴴ*resetKraus o₀ j=1 := by
  rw [resetKraus,Extraction.residualKraus_complete]
  simp

theorem resetKraus_apply (o₀ : ο) (X : Matrix ι ι ℂ) :
    Extraction.krausApply (resetKraus o₀) X=X.trace • Matrix.single o₀ o₀ 1 := by
  ext p q
  by_cases hp : p=o₀ <;> by_cases hq : q=o₀ <;>
    simp [resetKraus,Extraction.residualKraus,Extraction.krausApply,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,Matrix.sum_apply,
      hp,hq,Matrix.single,Matrix.trace,Matrix.diag] <;> aesop


theorem product_resetKraus (o₀ : ο) (p₀ : π) :
    Extraction.productKraus (resetKraus (ι := ι) o₀) (resetKraus (ι := α) p₀)=
      resetKraus (ι := ι×α) (o₀,p₀) := by
  ext ⟨i,j⟩ ⟨p,q⟩ ⟨x,y⟩
  by_cases hp : p=o₀ <;> by_cases hq : q=p₀ <;>
    by_cases hi : i=x <;> by_cases hj : j=y <;>
    simp [Extraction.productKraus,resetKraus,Extraction.residualKraus,
      Matrix.kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq,hp,hq,hi,hj]

/-- The two actual reset channels have Bell overlap Tr(X)/K. -/
theorem product_reset_bell_overlap (K : ℕ) (o₀ : Fin K)
    (X : Matrix (ι×α) (ι×α) ℂ) :
    (Extraction.bellProjector (d := Fin K)*Extraction.krausApply
      (Extraction.productKraus (resetKraus (ι := ι) o₀) (resetKraus (ι := α) o₀)) X).trace.re=
      X.trace.re/K := by
  letI : Nonempty (Fin K) := ⟨o₀⟩
  rw [product_resetKraus,resetKraus_apply,Matrix.mul_smul,Matrix.trace_smul,
    Matrix.trace_mul_single]
  simp only [MulOpposite.op_one,one_smul,smul_eq_mul,bellProjector_entry,
    eq_self_iff_true,and_self,ite_true,Fintype.card_fin]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_div]
  simp [Complex.mul_re,div_eq_mul_inv]
  left
  have hK : (K:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt o₀.isLt)
  field_simp [hK]
/-- Independent half mixtures at the two parties preserve a quarter of the
original overlap and, simultaneously, a deterministic-reset baseline. -/
theorem local_half_mix_fidelity_bounds (K : ℕ) (o₀ : Fin K)
    (A : τ → Matrix (Fin K) ι ℂ) (B : υ → Matrix (Fin K) α ℂ)
    (X : Matrix (ι×α) (ι×α) ℂ) (hX : X.PosSemidef) :
    let A' := halfMixKraus A (resetKraus o₀)
    let B' := halfMixKraus B (resetKraus o₀)
    let f := (Extraction.bellProjector (d := Fin K)*
      Extraction.krausApply (Extraction.productKraus A' B') X).trace.re
    (Extraction.bellProjector (d := Fin K)*
      Extraction.krausApply (Extraction.productKraus A B) X).trace.re/4 ≤ f ∧
      X.trace.re/(4*K) ≤ f := by
  classical
  letI : Nonempty (Fin K) := ⟨o₀⟩
  dsimp only
  let Q := Extraction.bellProjector (d := Fin K)
  have hp (C : τ → Matrix (Fin K) ι ℂ) (D : υ → Matrix (Fin K) α ℂ) :
      0 ≤ (Q*Extraction.krausApply (Extraction.productKraus C D) X).trace.re :=
    Extraction.positive_product_trace_re _ _ (Extraction.bellProjector_density (d := Fin K)).1
      (Extraction.krausApply_posSemidef _ _ hX)
  have h₀ := hp A B
  have h₁ := Extraction.positive_product_trace_re Q
    (Extraction.krausApply (Extraction.productKraus A (resetKraus (ι := α) o₀)) X)
    (Extraction.bellProjector_density (d := Fin K)).1
    (Extraction.krausApply_posSemidef _ _ hX)
  have h₂ := Extraction.positive_product_trace_re Q
    (Extraction.krausApply (Extraction.productKraus (resetKraus (ι := ι) o₀) B) X)
    (Extraction.bellProjector_density (d := Fin K)).1
    (Extraction.krausApply_posSemidef _ _ hX)
  have h₃ := Extraction.positive_product_trace_re Q
    (Extraction.krausApply (Extraction.productKraus (resetKraus (ι := ι) o₀)
      (resetKraus (ι := α) o₀)) X)
    (Extraction.bellProjector_density (d := Fin K)).1
    (Extraction.krausApply_posSemidef _ _ hX)
  have he := congrArg (fun M : Matrix (Fin K×Fin K) (Fin K×Fin K) ℂ => (Q*M).trace.re)
    (product_halfMixKraus_apply A (resetKraus (ι := ι) o₀) B (resetKraus (ι := α) o₀) X)
  simp only [Matrix.mul_smul,Matrix.mul_add,Matrix.trace_smul,Matrix.trace_add,
    Complex.add_re,smul_eq_mul,Complex.mul_re] at he
  norm_num at he
  constructor
  · change (Q*Extraction.krausApply (Extraction.productKraus A B) X).trace.re/4 ≤ _
    linarith
  · have hr := product_reset_bell_overlap (α := α) K o₀ X
    change (Q*Extraction.krausApply (Extraction.productKraus (resetKraus (ι := ι) o₀)
      (resetKraus (ι := α) o₀)) X).trace.re=X.trace.re/K at hr
    change X.trace.re/(4*K) ≤ (Q*
      Extraction.krausApply (Extraction.productKraus (halfMixKraus A (resetKraus o₀))
        (halfMixKraus B (resetKraus o₀))) X).trace.re
    rw [div_mul_eq_div_div,div_right_comm X.trace.re 4 (K:ℝ),← hr]
    linarith
end SpectralProtocol