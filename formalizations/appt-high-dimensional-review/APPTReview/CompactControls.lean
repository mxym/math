import APPTReview.PurityInterval

open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
open Matrix
namespace APPTReviewCompactControls

/-- A nonzero nilpotent matrix has trace-square zero: Hermiticity cannot be dropped. -/
def nilpotent : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ :=
  fun i j => if i.2=0 ∧ j.2=1 then 1 else 0

theorem nilpotent_sq : nilpotent*nilpotent=0 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;>
    norm_num [nilpotent, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem nilpotent_purity_zero : APPT.Quantum.purity nilpotent=0 := by
  simp [APPT.Quantum.purity, nilpotent_sq]

theorem nilpotent_ne_zero : nilpotent≠0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ => A (0,0) (0,1)) h
  norm_num [nilpotent] at hh

theorem nilpotent_not_hermitian : ¬nilpotent.IsHermitian := by
  intro h
  exact nilpotent_ne_zero ((APPTReview.hermitian_purity_zero_iff h).mp nilpotent_purity_zero)

/-- A zero-dimensional product cannot supply a trace-one density matrix. -/
theorem zero_dimension_no_density (n : ℕ)
    (A : Matrix (Fin 0 × Fin n) (Fin 0 × Fin n) ℂ) : ¬APPT.Quantum.IsDensity A := by
  intro h
  have ht := h.2
  simp [Matrix.trace] at ht

/-- A real APPT value strictly exceeds the minimum in 2x2 dimensions. -/
theorem two_by_two_nonuniform_exists :
    ∃ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A=1/3 := by
  obtain ⟨A,hA,hP,he⟩ := APPTReview.exists_projectionPlateau (by norm_num : 2≤2)
    (by norm_num : 0<2) 1 (by norm_num : 1≤2*2)
  refine ⟨A,hA,hP,?_⟩
  norm_num [APPTReview.plateauDenominator] at he
  exact he

/-- Strictly positive mixture weights are necessary for optimizer rigidity. -/
theorem zero_weight_rigidity_fails :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.IsDensity B ∧ APPT.Quantum.AbsolutelyPPT B ∧ A≠B ∧
      APPT.Quantum.purity (APPTReview.stateMix 0 A B)=APPTReview.apptPuritySup 2 2 := by
  obtain ⟨A,hA,hP,he⟩ := APPTReview.exists_appt_purity_eq_sup (by norm_num : 2≤2) (by norm_num : 2≤2)
  let B := APPTReview.maximallyMixed 2 2
  have hB := APPTReview.maximallyMixed_density (by norm_num : 0<2) (by norm_num : 0<2)
  have hQ := APPTReview.maximallyMixed_appt 2 2
  have hlow : (1/3:ℝ)≤APPTReview.apptPuritySup 2 2 := by
    obtain ⟨C,hC,hR,hc⟩ := two_by_two_nonuniform_exists
    exact le_csSup (APPTReview.appt_purity_values_nonempty_bounded (by norm_num : 2≤2) (by norm_num : 2≤2)).2
      ⟨C,hC,hR,hc.symm⟩
  have hneq : A≠B := by
    intro h
    have hb : APPT.Quantum.purity B=1/4 := by
      convert APPTReview.maximallyMixed_purity (by norm_num : 0<2) (by norm_num : 0<2) using 1 <;> norm_num [B]
    rw [h,hb] at he
    linarith
  refine ⟨A,B,hA,hP,hB,hQ,hneq,?_⟩
  simpa [APPTReview.stateMix] using he

end APPTReviewCompactControls
