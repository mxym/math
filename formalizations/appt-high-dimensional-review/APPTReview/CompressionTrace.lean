import APPTReview.SchmidtJointWitness

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Trace of a product of positive matrices is real-nonnegative, without commuting them. -/
theorem positive_product_trace_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0≤(P*Q).trace.re := by
  let U := hP.isHermitian.eigenvectorUnitary
  have hdiag (i : ι) : 0≤(((U:Matrix ι ι ℂ)ᴴ*Q*(U:Matrix ι ι ℂ)) i i).re :=
    (RCLike.nonneg_iff.mp ((hQ.conjTranspose_mul_mul_same (U:Matrix ι ι ℂ)).diag_nonneg)).1
  have hp := hP.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal,Function.comp_def] at hp
  rw [Matrix.trace_mul_comm,hp,trace_congruence_diagonal]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hdiag i) (hP.eigenvalues_nonneg i))

/-- The compression does not increase trace: this is the rank-budget bridge,
not a hypothesis that the compressed diagonal already has the desired mass. -/
theorem compression_trace_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (hP : P.PosSemidef) (hL : (1-L*Lᴴ).PosSemidef) :
    (Lᴴ*P*L).trace.re≤P.trace.re := by
  have h := positive_product_trace_re P (1-L*Lᴴ) hP hL
  have he : (P*(L*Lᴴ)).trace=(Lᴴ*P*L).trace := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_sub,Matrix.mul_one,Matrix.trace_sub,Complex.sub_re] at h
  rw [he] at h
  linarith

noncomputable def compressionDiagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (L : Matrix ι κ ℂ) : κ → ℝ := fun i => ((Lᴴ*P*L) i i).re

/-- A positive contraction supplies actual fractional weights in [0,1],
whose full mass is bounded by its physical trace. -/
theorem compressionDiagonal_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) (hL : (1-L*Lᴴ).PosSemidef) :
    (∀ i,0≤compressionDiagonal P L i) ∧ (∀ i,compressionDiagonal P L i≤1) ∧
    (∑ i,compressionDiagonal P L i)≤P.trace.re := by
  obtain ⟨hQ,hQI⟩ := compression_positive_contraction P L hP hI hL
  refine ⟨fun i => (RCLike.nonneg_iff.mp hQ.diag_nonneg).1,?_,?_⟩
  · intro i
    have h := (RCLike.nonneg_iff.mp (hQI.diag_nonneg (i:=i))).1
    simpa [compressionDiagonal,Matrix.sub_apply,Matrix.one_apply] using h
  · simpa only [compressionDiagonal,Matrix.trace,Matrix.diag_apply,Complex.re_sum] using compression_trace_le P L hP hL

end APPTReview
