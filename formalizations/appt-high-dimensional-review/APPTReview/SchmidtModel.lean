import APPTReview.SchmidtDiagonal
import APPTReview.QuantumTrace

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

/-- Diagonal pure-state partial-transpose model with all signed eigenvalues explicit. -/
theorem exists_pure_partialTranspose_diagonal (v : a × b → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) :
    ∃ (s : a → ℝ) (L : Matrix (a × b) (a × a) ℂ),
      (∀ i, 0≤s i) ∧ (∑ i, (s i)^2)=1 ∧
      (1-L*Lᴴ).PosSemidef ∧
      APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v))=
        L*Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*Lᴴ := by
  obtain ⟨s,K,hs,hss,hK,hW⟩ := exists_pure_partialTranspose_model v hv
  let L := K*hadamard (a:=a)
  have he : L*Lᴴ=K*Kᴴ := by
    calc
      _ = K*(hadamard (a:=a)*hadamard)*Kᴴ := by
        simp only [L,Matrix.conjTranspose_mul,hadamard_conjTranspose,Matrix.mul_assoc]
      _ = _ := by rw [hadamard_sq,Matrix.mul_one]
  refine ⟨s,L,hs,hss,by rwa [he],?_⟩
  rw [hW,schmidtExchange_diagonalization]
  simp only [L,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- The trace of a positive contraction against a signed diagonal congruence
is bounded by the explicit sum of its negative eigenvalue magnitudes. -/
theorem trace_contraction_diagonal_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (d neg : κ → ℝ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (hL : (1-L*Lᴴ).PosSemidef) (hn : ∀ i,0≤neg i) (hd : ∀ i,0≤d i+neg i) :
    -(∑ i,neg i) ≤ (P*(L*Matrix.diagonal (fun i => (d i:ℂ))*Lᴴ)).trace.re := by
  obtain ⟨hQ,hQI⟩ := compression_positive_contraction P L hP hI hL
  have hlo (i : κ) : 0≤(Lᴴ*P*L) i i := hQ.diag_nonneg
  have hhi (i : κ) : 0≤(1-Lᴴ*P*L : Matrix κ κ ℂ) i i := hQI.diag_nonneg
  have hb (i : κ) : -(neg i) ≤ ((Lᴴ*P*L) i i).re*d i := by
    have h0 : 0≤((Lᴴ*P*L) i i).re := (RCLike.nonneg_iff.mp (hlo i)).1
    have h1 : ((Lᴴ*P*L) i i).re≤1 := by
      have hh := (RCLike.nonneg_iff.mp (hhi i)).1
      simpa [Matrix.sub_apply,Matrix.one_apply] using hh
    have ha := mul_nonneg (hd i) h0
    have hc := mul_nonneg (hn i) (sub_nonneg.mpr h1)
    nlinarith
  rw [trace_congruence_diagonal]
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero,Finset.sum_neg_distrib] using Finset.sum_le_sum
      (fun i (_ : i∈Finset.univ) => hb i)

end APPTReview
