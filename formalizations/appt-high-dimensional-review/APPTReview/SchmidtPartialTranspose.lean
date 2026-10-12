import APPTReview.SchmidtFrame

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Pure-state outer product of a coefficient matrix in the actual product basis. -/
def rowPure (T : Matrix a b ℂ) : Matrix (a × b) (a × b) ℂ :=
  fun p q => T p.1 p.2 * star (T q.1 q.2)

/-- The weighted exchange block of a pure-state partial transpose. -/
def schmidtExchange (s : a → ℝ) : Matrix (a × a) (a × a) ℂ :=
  fun p q => if p.swap=q then (s p.1:ℂ)*(s p.2:ℂ) else 0

theorem schmidtExchange_hermitian (s : a → ℝ) : (schmidtExchange s).IsHermitian := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hi : i=l <;> by_cases hj : j=k <;>
    simp_all [Matrix.conjTranspose_apply,schmidtExchange,eq_comm,mul_comm]

theorem schmidt_congruence_apply {d : Type*} [Fintype d]
    (K : Matrix d (a × a) ℂ) (s : a → ℝ) (i j : d) :
    (K*schmidtExchange s*Kᴴ) i j=
      ∑ p : a × a, K i p*(s p.1:ℂ)*(s p.2:ℂ)*star (K j p.swap) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply,schmidtExchange,Matrix.conjTranspose_apply,ite_mul,mul_assoc]

/-- Exact Schmidt factorization of the partial transpose, with original complex entries. -/
theorem partialTranspose_rowPure_eq_schmidt (T : Matrix a b ℂ)
    (U : Matrix.unitaryGroup a ℂ) (s : a → ℝ) (Z : Matrix a b ℂ)
    (hT : T=(U:Matrix a a ℂ)*Matrix.diagonal (fun i => (s i:ℂ))*Z) :
    APPT.Quantum.partialTranspose (rowPure T)=
      schmidtFrame U Z*schmidtExchange s*(schmidtFrame U Z)ᴴ := by
  have ht (i : a) (x : b) : T i x=∑ j, (U:Matrix a a ℂ) i j*(s j:ℂ)*Z j x := by
    rw [hT,Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [schmidt_congruence_apply,Fintype.sum_prod_type]
  change T j x*star (T i y)=_
  rw [ht j x,ht i y]
  simp only [schmidtFrame_apply,Prod.fst,Prod.snd,Prod.swap,star_sum,star_mul,
    star_star,Finset.sum_mul,Finset.mul_sum]
  simp only [RCLike.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Every normalized pure test has a genuine contraction model. No Schmidt data
are supplied as hypotheses and zero singular values are explicitly accommodated. -/
theorem exists_pure_partialTranspose_model (v : a × b → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) :
    ∃ (s : a → ℝ) (K : Matrix (a × b) (a × a) ℂ),
      (∀ i, 0≤s i) ∧ (∑ i, (s i)^2)=1 ∧
      (1-K*Kᴴ).PosSemidef ∧
      APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v))=
        K*schmidtExchange s*Kᴴ := by
  let T : Matrix a b ℂ := fun i x => v (i,x)
  obtain ⟨U,s,Z,hs,hT,hZ,hsum⟩ := exists_schmidt_rows T
  have htr : (T*Tᴴ).trace=1 := by
    change (∑ i : a, ∑ x : b, v (i,x)*star (v (i,x)))=1
    simpa [Fintype.sum_prod_type,mul_comm] using hv
  refine ⟨s,schmidtFrame U Z,hs,?_,schmidtFrame_contraction U s Z hZ,?_⟩
  · rw [hsum,htr]
    rfl
  · exact partialTranspose_rowPure_eq_schmidt T U s Z hT

end APPTReview
