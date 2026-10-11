import APPTReview.BoundarySpectrum

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReviewRegression

example : Function.Injective (APPTReview.rankTwoLabels (by decide : 4 ≤ 4)) :=
  APPTReview.rankTwoLabels_injective _
example : ¬ Function.Injective (fun _ : Fin 4 => (0 : Fin 4)) := by decide
example : (APPTReview.paperPivot (k:=0) (n:=2) (by omega)).val = 1 := rfl
example : (APPTReview.paperPivot (k:=1) (n:=3) (by omega)).val = 3 := rfl
set_option maxRecDepth 4096 in
example : (APPTReview.paperPivot (k:=8) (n:=38) (by omega)).val = 325 := rfl

def productWeight (p : Fin 2 × Fin 2) : ℝ := if p=(0,0) then 1 else 0
def productState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun p => (productWeight p : ℂ))

theorem productState_density : APPT.Quantum.IsDensity productState := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro p
    simp only [productWeight]
    split_ifs <;> norm_num
  · simp [productState, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, productWeight]

theorem productState_ppt : (APPT.Quantum.partialTranspose productState).PosSemidef := by
  have he : APPT.Quantum.partialTranspose productState=productState := by
    ext p q
    rcases p with ⟨i,j⟩
    rcases q with ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [APPT.Quantum.partialTranspose, productState, productWeight, Matrix.diagonal]
  rw [he]
  exact productState_density.1

/-- An actual trace-one PSD and PPT state is not APPT. The all-unitary hypothesis
cannot be dropped from the sorted witness and entropy consequences. -/
theorem productState_not_appt : ¬ APPT.Quantum.AbsolutelyPPT productState := by
  intro h
  let σ : Equiv.Perm (Fin 2 × Fin 2) := Equiv.swap (0,0) (1,0)
  have hM := APPTReview.diagonal_appt_witness_posSemidef
    (fun p => productWeight (σ p))
    (APPTReview.diagonal_appt_permute productWeight h σ) id Function.injective_id
  have hq := hM.dotProduct_mulVec_nonneg (fun _ : Fin 2 => (1 : ℝ))
  norm_num [APPTReview.witnessMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    productWeight, σ, Equiv.swap_apply_def] at hq

end APPTReviewRegression