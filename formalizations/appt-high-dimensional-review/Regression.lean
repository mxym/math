import APPTReview.FinitePurity
import APPTReview.RowArrangement
import APPTReview

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

/-- Concrete physical existence at a rectangular parameter pair, from the generic proof. -/
theorem plateau_four_fiftyeight :
    ∃ A : Matrix (Fin 4 × Fin 58) (Fin 4 × Fin 58) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A = 2/435 := by
  have hh := APPTReview.exists_projectionPlateau (m:=4) (n:=58)
    (by norm_num) (by norm_num) 87 (by norm_num)
  norm_num [APPTReview.plateauDenominator] at hh
  exact hh

end APPTReviewRegression
namespace APPTReviewGraphRegression
open scoped BigOperators
open Matrix

def signedGraph : Matrix (Fin 1) (Fin 1) ℝ := (-2 : ℝ) • 1

theorem signedGraph_upper_cap : ((1 : Matrix (Fin 1) (Fin 1) ℝ)-signedGraph).PosSemidef := by
  have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef).smul
    (by norm_num : (0 : ℝ)≤3)
  convert h using 1
  unfold signedGraph
  module

theorem signedGraph_square_failure : ¬ (∑ i : Fin 1, (signedGraph *ᵥ (fun _ => (1:ℝ))) i ^ 2) ≤ 1 := by
  norm_num [signedGraph, Matrix.mulVec, Matrix.smul_apply, Matrix.one_apply, dotProduct]

def lateEdge : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) then 1 else 0

theorem unordered_triangle_failure :
    ¬ (3 : ℝ)*(∑ i : Fin 2, APPTReview.rowEnergy lateEdge i.succ) ≤
      ∑ i : Fin 3, (∑ j : Fin 3, lateEdge i j)^2 := by
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num [APPTReview.rowEnergy, h1, h2, lateEdge]


end APPTReviewGraphRegression

namespace APPTReviewFiniteRegression
open scoped BigOperators
theorem sum_baseline_multiplicity_control :
    (∑ _i : Fin 3, ((2 : ℝ)-1)) ≠ (∑ _i : Fin 3, (2 : ℝ))-1 := by norm_num
theorem aspect_term_cannot_be_omitted :
    (3 : ℝ)/(8*300)-1/(3*300) > 8*(1/(4*300))^2 := by norm_num
end APPTReviewFiniteRegression
