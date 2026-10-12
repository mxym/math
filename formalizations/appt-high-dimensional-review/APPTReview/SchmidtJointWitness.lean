import APPTReview.SchmidtJointScalar

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

/-- Full signed contraction model for every test vector, including zero. -/
theorem exists_pure_signed_model (v : a × b → ℂ) :
    ∃ (s : a → ℝ) (L : Matrix (a × b) (a × a) ℂ),
      (∀ i,0≤s i) ∧ (∑ i,(s i)^2)=(star v ⬝ᵥ v).re ∧
      (1-L*Lᴴ).PosSemidef ∧
      APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v))=
        L*Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*Lᴴ := by
  let T : Matrix a b ℂ := fun i x => v (i,x)
  obtain ⟨U,s,Z,hs,hT,hZ,hss⟩ := exists_schmidt_rows T
  let K := schmidtFrame U Z
  let L := K*hadamard (a:=a)
  have hK := schmidtFrame_contraction U s Z hZ
  have hLL : L*Lᴴ=K*Kᴴ := by
    simp only [L,Matrix.conjTranspose_mul,hadamard_conjTranspose]
    calc
      _ = K*(hadamard (a:=a)*hadamard)*Kᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hadamard_sq,Matrix.mul_one]
  have ht : (T*Tᴴ).trace=star v ⬝ᵥ v := by
    change (∑ i,∑ x,v (i,x)*star (v (i,x)))=∑ p,star (v p)*v p
    simp only [Fintype.sum_prod_type,mul_comm]
  refine ⟨s,L,hs,by rwa [ht] at hss,by rwa [hLL],?_⟩
  have he := partialTranspose_rowPure_eq_schmidt T U s Z hT
  change APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v))=K*schmidtExchange s*Kᴴ at he
  rw [he,schmidtExchange_diagonalization]
  simp only [L,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- The same Schmidt data control contraction trace and the spike floor jointly. -/
theorem pure_joint_witness (hc : 4≤Fintype.card a)
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.PosSemidef) (hI : (1-P).PosSemidef)
    (x : a × b → ℂ) :
    ∃ N : ℝ, 0≤N ∧
      -N≤(P*APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).trace.re ∧
      ((((2*(Fintype.card a:ℝ)-5)*(star x ⬝ᵥ x).re-2*N) •
        (1 : Matrix (a × b) (a × b) ℂ))+
        (4*((Fintype.card a:ℝ)-4)) • APPT.Quantum.partialTranspose (Matrix.vecMulVec x (star x))).PosSemidef := by
  obtain ⟨s,L,hs,hss,hL,hW⟩ := exists_pure_signed_model x
  refine ⟨schmidtMass s,schmidtMass_nonneg s hs,?_,?_⟩
  · rw [hW]
    exact trace_contraction_diagonal_lower P L (schmidtSigned s) (schmidtNegative s)
      hP hI hL (schmidtNegative_nonneg s hs) (schmidtSigned_add_negative_nonneg s hs)
  · rw [hW,← hss]
    exact diagonal_floor_lift L (schmidtSigned s) _ _
      (schmidt_joint_background s hc) hL (schmidt_joint_signed_nonneg s hc hs)

end APPTReview
