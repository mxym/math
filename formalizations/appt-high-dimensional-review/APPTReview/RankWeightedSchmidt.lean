import APPTReview.CompressionTrace

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

noncomputable def negativeCompressionWeight (q : a × a → ℝ) (p : a × a) : ℝ :=
  if p.2<p.1 then q p else 0

noncomputable def symmetricCompressionWeight (q : a × a → ℝ) (p : a × a) : ℝ :=
  negativeCompressionWeight q p+negativeCompressionWeight q p.swap

theorem symmetricCompressionWeight_bounds (q : a × a → ℝ)
    (hq : ∀ p,0≤q p) (hq1 : ∀ p,q p≤1) :
    (∀ p,0≤symmetricCompressionWeight q p) ∧
    (∀ p,symmetricCompressionWeight q p≤1) ∧
    (∀ i j,symmetricCompressionWeight q (i,j)=symmetricCompressionWeight q (j,i)) ∧
    (∀ i,symmetricCompressionWeight q (i,i)=0) := by
  have h0 (p) : 0≤negativeCompressionWeight q p := by
    unfold negativeCompressionWeight; split_ifs; exact hq p; exact le_rfl
  refine ⟨fun p => add_nonneg (h0 p) (h0 p.swap),?_,?_,?_⟩
  · intro ⟨i,j⟩
    rcases lt_trichotomy i j with h | h | h
    · simpa [symmetricCompressionWeight,negativeCompressionWeight,h,not_lt_of_gt h] using hq1 (j,i)
    · subst j; simp [symmetricCompressionWeight,negativeCompressionWeight]
    · simpa [symmetricCompressionWeight,negativeCompressionWeight,h,not_lt_of_gt h] using hq1 (i,j)
  · intro i j; unfold symmetricCompressionWeight; simp only [Prod.swap]; ring
  · intro i; simp [symmetricCompressionWeight,negativeCompressionWeight]

theorem symmetricCompressionWeight_mass (q : a × a → ℝ) (hq : ∀ p,0≤q p) :
    (∑ p,symmetricCompressionWeight q p)≤2*∑ p,q p := by
  have hswap : (∑ p : a × a,negativeCompressionWeight q p.swap)=(∑ p,negativeCompressionWeight q p) := (Equiv.prodComm a a).sum_comp (negativeCompressionWeight q)
  have hle := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
    show negativeCompressionWeight q p≤q p by
      unfold negativeCompressionWeight; split_ifs; exact le_rfl; exact hq p)
  simp only [symmetricCompressionWeight,Finset.sum_add_distrib,hswap]
  linarith

theorem symmetricCompressionWeight_pairing (q : a × a → ℝ) (s : a → ℝ) :
    (∑ p,symmetricCompressionWeight q p*(s p.1*s p.2))=
      2*∑ p,q p*schmidtNegative s p := by
  have hswap := (Equiv.prodComm a a).sum_comp
    (fun p : a × a => negativeCompressionWeight q p*(s p.1*s p.2))
  have he (p : a × a) : negativeCompressionWeight q p*(s p.1*s p.2)=q p*schmidtNegative s p := by
    unfold negativeCompressionWeight schmidtNegative
    split_ifs <;> simp
  have hs : (∑ p : a × a, negativeCompressionWeight q p.swap*(s p.1*s p.2))=
      ∑ p : a × a,negativeCompressionWeight q p*(s p.1*s p.2) := by
    change (∑ p : a × a, negativeCompressionWeight q p.swap*(s p.2*s p.1))=∑ p : a × a,negativeCompressionWeight q p*(s p.1*s p.2) at hswap
    simpa only [mul_comm] using hswap
  simp only [symmetricCompressionWeight,add_mul,Finset.sum_add_distrib,hs]
  simp_rw [he]
  ring

/-- Rank-sensitive physical trace inequality with a constructed fractional graph.
All contractions may use the same Schmidt frame; its mass bound is proved. -/
theorem compressed_schmidt_rank_witness {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (L : Matrix ι (a × a) ℂ) (s : a → ℝ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) (hL : (1-L*Lᴴ).PosSemidef)
    (hs : ∀ i,0≤s i) :
    let w := symmetricCompressionWeight (compressionDiagonal P L)
    (∀ p,0≤w p) ∧ (∀ p,w p≤1) ∧ (∀ i j,w (i,j)=w (j,i)) ∧
    (∀ i,w (i,i)=0) ∧ (∑ p,w p)≤2*P.trace.re ∧
    -(1/2)*(∑ p,w p*(s p.1*s p.2)) ≤
      (P*(L*Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*Lᴴ)).trace.re := by
  dsimp only
  obtain ⟨hq,hq1,hqm⟩ := compressionDiagonal_budget P L hP hI hL
  obtain ⟨hw,hw1,hws,hwd⟩ := symmetricCompressionWeight_bounds (compressionDiagonal P L) hq hq1
  refine ⟨hw,hw1,hws,hwd,?_,?_⟩
  · exact (symmetricCompressionWeight_mass _ hq).trans (by linarith)
  · rw [symmetricCompressionWeight_pairing,trace_congruence_diagonal]
    simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hp (p : a × a) : -(compressionDiagonal P L p*schmidtNegative s p)≤
        compressionDiagonal P L p*schmidtSigned s p := by
      have h := mul_nonneg (hq p) (schmidtSigned_add_negative_nonneg s hs p)
      nlinarith
    have hh := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hp p)
    simp only [Finset.sum_neg_distrib,compressionDiagonal] at hh
    dsimp only [compressionDiagonal]
    linarith

end APPTReview
