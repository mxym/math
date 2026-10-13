import APPTSubunit.NegativeState

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTSubunit
open APPTReview

def negativeEvenSupport : Finset (Fin 3 × Fin 12) :=
  Finset.univ.filter (fun p => 1≤12*p.1.val+p.2.val ∧ 12*p.1.val+p.2.val<19)

theorem negative_even_support_card : negativeEvenSupport.card=18 := by decide +kernel

theorem negative_even_physical_control :
    APPT.Quantum.IsDensity (negativeState 1 negativeEvenSupport (0,0)) ∧
    APPT.Quantum.AbsolutelyPPT (negativeState 1 negativeEvenSupport (0,0)) ∧
    APPT.Quantum.purity (negativeState 1 negativeEvenSupport (0,0))=(1765/61009:ℝ) := by
  refine ⟨negativeState_density (by decide) (by decide) 1 (by norm_num) (by norm_num) _ _,
    negativeState_appt (by decide) (by decide) 1 (by norm_num) (by norm_num) _ _,?_⟩
  rw [negativeState_purity 1 _ _ (by decide),negative_even_support_card]
  norm_num [negativePurity,negativeTrace,negativeBackground]

noncomputable def naiveNegativeWeight (p : Fin 2 × Fin 2) : ℝ :=
  if p=(0,0) then 0 else if p=(1,0) then 3/7 else 2/7

noncomputable def naiveNegativeDensity : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun p => (naiveNegativeWeight p:ℂ))

/-- Deleting the finite h² reserve leaves a genuine density matrix. -/
theorem naiveNegative_density : APPT.Quantum.IsDensity naiveNegativeDensity := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro p
    change (0:ℂ)≤(naiveNegativeWeight p:ℂ)
    apply RCLike.nonneg_iff.mpr
    constructor
    · change (0:ℝ)≤naiveNegativeWeight p
      by_cases he : p=(0,0) <;> by_cases hf : p=(1,0) <;> norm_num [naiveNegativeWeight,he,hf]
    · simp
  · norm_num [naiveNegativeDensity,Matrix.trace_diagonal,Fintype.sum_prod_type,
      Fin.sum_univ_two,naiveNegativeWeight]

/-- The missing reserve cannot be replaced by its limiting zero value:
an exact original APPT orbit test is negative. -/
theorem naiveNegative_not_appt : ¬APPT.Quantum.AbsolutelyPPT naiveNegativeDensity := by
  intro hp
  have hw := diagonal_appt_witness_posSemidef naiveNegativeWeight hp
    (id : Fin 2 → Fin 2) Function.injective_id
  have hq := hw.dotProduct_mulVec_nonneg (fun i : Fin 2 => if i=0 then (4:ℝ) else 1)
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two,witnessMatrix,naiveNegativeWeight] at hq

end APPTSubunit
