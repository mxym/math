import APPTReview.Counterexample1038
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
noncomputable def proposedAPPTPurity (m n : ℕ) : ℝ :=
  let D : ℝ := (m:ℝ)*n
  let t : ℕ := ((m-1)*n+1)/2
  max ((D+8)/(D+2)^2) ((D*((m:ℝ)-1)^2+4*m*t)/(D*((m:ℝ)-1)+2*t)^2)
theorem counterexample1038_formula_gap :
    proposedAPPTPurity 10 38 < APPT.Quantum.purity counterexample1038 := by
  rw [counterexample1038_purity]
  norm_num [proposedAPPTPurity]
theorem not_proposedAPPTPurity_upper :
    ¬ (∀ (m n : ℕ), 2≤m → m≤n → 2<n →
      ∀ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A → APPT.Quantum.AbsolutelyPPT A →
      APPT.Quantum.purity A≤proposedAPPTPurity m n) := by
  intro h
  exact (not_le_of_gt counterexample1038_formula_gap)
    (h 10 38 (by omega) (by omega) (by omega) counterexample1038
      counterexample1038_isDensity counterexample1038_absolutelyPPT)
theorem joint_scalar_boundary_and_failure :
    let s : Fin 10 → ℝ := fun i => if i.val<2 then 4 else 1
    15*(∑ i,(s i)^2)-2*schmidtMass s-24*s 0*s 1=0 ∧
    15*(∑ i,(s i)^2)-2*schmidtMass s-25*s 0*s 1= -16 := by
  dsimp only
  rw [schmidtMass_identity]
  norm_num [Fin.sum_univ_succ]
theorem zero_schmidt_model :
    ∃ (s : Fin 4 → ℝ) (L : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 4) ℂ),
      (∀ i,0≤s i) ∧ (∑ i,(s i)^2)=0 ∧ (1-L*Lᴴ).PosSemidef ∧
        L*Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*Lᴴ=0 := by
  obtain ⟨s,L,hs,hss,hL,hW⟩ := exists_pure_signed_model (0 : Fin 4 × Fin 1 → ℂ)
  refine ⟨s,L,hs,by simpa using hss,hL,?_⟩
  calc
    _ = APPT.Quantum.partialTranspose (Matrix.vecMulVec (0 : Fin 4 × Fin 1 → ℂ) (star 0)) := hW.symm
    _ = 0 := by ext i j; simp [Matrix.vecMulVec,APPT.Quantum.partialTranspose]
end APPTReview
