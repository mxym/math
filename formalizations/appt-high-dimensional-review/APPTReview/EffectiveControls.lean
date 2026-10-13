import APPTReview.WideAsymptotic

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

def effectiveEvenSupport : Finset (Fin 6 × Fin 24) :=
  Finset.univ.filter (fun p => 24*p.1.val+p.2.val<72)

theorem effective_even_support_card : effectiveEvenSupport.card=72 := by decide +kernel

theorem effective_even_physical_regression :
    APPT.Quantum.IsDensity (effectiveState 1 effectiveEvenSupport (0,0)) ∧
    APPT.Quantum.AbsolutelyPPT (effectiveState 1 effectiveEvenSupport (0,0)) ∧
    APPT.Quantum.purity (effectiveState 1 effectiveEvenSupport (0,0))=(1565/223494:ℝ) := by
  refine ⟨effectiveState_density (by decide) (by decide) 1 (by norm_num) _ _,
    effectiveState_appt (by decide) (by decide) 1 (by norm_num) _ _,?_⟩
  rw [effectiveState_purity 1 _ _ (by decide),effective_even_support_card]
  norm_num [effectivePurity,effectiveTrace,effectiveBackground]

def effectiveOddSupport : Finset (Fin 7 × Fin 29) :=
  Finset.univ.filter (fun p => 29*p.1.val+p.2.val<102)

theorem effective_odd_support_card : effectiveOddSupport.card=102 := by decide +kernel

theorem effective_odd_physical_regression :
    APPT.Quantum.IsDensity (effectiveState 1 effectiveOddSupport (0,0)) ∧
    APPT.Quantum.AbsolutelyPPT (effectiveState 1 effectiveOddSupport (0,0)) ∧
    APPT.Quantum.purity (effectiveState 1 effectiveOddSupport (0,0))=(66739/13461561:ℝ) := by
  refine ⟨effectiveState_density (by decide) (by decide) 1 (by norm_num) _ _,
    effectiveState_appt (by decide) (by decide) 1 (by norm_num) _ _,?_⟩
  rw [effectiveState_purity 1 _ _ (by decide),effective_odd_support_card]
  norm_num [effectivePurity,effectiveTrace,effectiveBackground]

/-- A fixed finite construction is not silently identified with its limiting coefficient. -/
theorem effective_finite_not_limit :
    (144:ℝ)^2*(APPT.Quantum.purity (effectiveState 1 effectiveEvenSupport (0,0))-1/144)<8 := by
  rw [effective_even_physical_regression.2.2]
  norm_num

noncomputable def naiveEffectiveWeight (p : Fin 2 × Fin 2) : ℝ :=
  if p=(1,0) then 13/25 else 4/25

noncomputable def naiveEffectiveDensity : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun p => (naiveEffectiveWeight p:ℂ))

/-- Removing the finite interaction reserve produces a genuine density matrix. -/
theorem naiveEffective_density : APPT.Quantum.IsDensity naiveEffectiveDensity := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro p
    change (0:ℂ)≤(naiveEffectiveWeight p:ℂ)
    apply RCLike.nonneg_iff.mpr
    constructor
    · change (0:ℝ)≤naiveEffectiveWeight p
      by_cases he : p=(1,0) <;> norm_num [naiveEffectiveWeight,he]
    · simp
  · norm_num [naiveEffectiveDensity,Matrix.trace_diagonal,Fintype.sum_prod_type,
      Fin.sum_univ_two,naiveEffectiveWeight]

/-- The same actual density is not APPT: an exact Hadamard orbit supplies the negative test. -/
theorem naiveEffective_not_appt : ¬APPT.Quantum.AbsolutelyPPT naiveEffectiveDensity := by
  intro hp
  have hw := diagonal_appt_witness_posSemidef naiveEffectiveWeight hp
    (id : Fin 2 → Fin 2) Function.injective_id
  have hq := hw.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  norm_num [dotProduct,Matrix.mulVec,Fin.sum_univ_two,witnessMatrix,naiveEffectiveWeight] at hq

end APPTReview
