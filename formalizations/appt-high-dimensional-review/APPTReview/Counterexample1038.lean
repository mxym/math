import APPTReview.JointSufficiency

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem setProjection_mul_subset (s t : Finset ι) (hts : t⊆s) :
    setProjection s*setProjection t=setProjection t := by
  simp only [setProjection,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i∈t
  · simp [hi,hts hi]
  · simp [hi]

theorem pure_single_eq_setProjection (e : ι) :
    Matrix.vecMulVec (Pi.single e (1:ℂ)) (star (Pi.single e (1:ℂ)))=setProjection {e} := by
  ext i j
  by_cases hi : i=e <;> by_cases hj : j=e <;>
    simp_all [Matrix.vecMulVec,setProjection,Matrix.diagonal_apply,Pi.single_apply,eq_comm]

/-- Product-coordinate order: the first 147 entries have the middle increment. -/
def counterexample1038Support : Finset (Fin 10 × Fin 38) :=
  Finset.univ.filter (fun p => 38*p.1.val+p.2.val<147)

theorem counterexample1038Support_card : counterexample1038Support.card=147 := by
  decide +kernel

theorem counterexample1038Support_zero : (0,0)∈counterexample1038Support := by
  decide

noncomputable def counterexample1038Base : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ :=
  (15:ℝ) • 1+(2:ℝ) • setProjection counterexample1038Support+
    (24:ℝ) • setProjection {(0,0)}

noncomputable def counterexample1038 : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ :=
  (1/6018:ℝ) • counterexample1038Base

theorem counterexample1038Base_as_joint : counterexample1038Base=
    jointSpike (setProjection counterexample1038Support) (Pi.single (0,0) (1:ℂ)) := by
  rw [jointSpike,pure_single_eq_setProjection]
  norm_num [counterexample1038Base]

/-- Actual all-unitary APPT membership of the original 380-dimensional counterexample. -/
theorem counterexample1038_absolutelyPPT : APPT.Quantum.AbsolutelyPPT counterexample1038 := by
  unfold counterexample1038
  apply APPT.Quantum.absolutelyPPT_smul
  · rw [counterexample1038Base_as_joint]
    apply jointSpike_absolutelyPPT (by norm_num)
    · exact hermitian_idempotent_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · exact hermitian_idempotent_complement_posSemidef _ (setProjection_hermitian _) (setProjection_sq _)
    · simp [dotProduct,Pi.single_apply]
  · norm_num

theorem counterexample1038Base_trace : counterexample1038Base.trace=6018 := by
  norm_num [counterexample1038Base,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,
    setProjection_trace,counterexample1038Support_card,Complex.real_smul]

theorem counterexample1038_isDensity : APPT.Quantum.IsDensity counterexample1038 := by
  constructor
  · have hP := hermitian_idempotent_posSemidef (setProjection counterexample1038Support)
      (setProjection_hermitian _) (setProjection_sq _)
    have hR := hermitian_idempotent_posSemidef (setProjection ({(0,0)}:Finset (Fin 10 × Fin 38)))
      (setProjection_hermitian _) (setProjection_sq _)
    exact (((Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ)≤15)).add
      (hP.smul (by norm_num : (0:ℝ)≤2))).add
      (hR.smul (by norm_num : (0:ℝ)≤24))).smul (by norm_num : (0:ℝ)≤1/6018)
  · norm_num [counterexample1038,Matrix.trace_smul,counterexample1038Base_trace,Complex.real_smul]

theorem counterexample1038Base_sq : counterexample1038Base*counterexample1038Base=
    (225:ℝ) • (1 : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ)+
      (64:ℝ) • setProjection counterexample1038Support+(1392:ℝ) • setProjection {(0,0)} := by
  have hsub : ({(0,0)}:Finset (Fin 10 × Fin 38))⊆counterexample1038Support := by
    simpa using counterexample1038Support_zero
  have hPR := setProjection_mul_subset _ _ hsub
  have hRP : setProjection ({(0,0)}:Finset (Fin 10 × Fin 38))*setProjection counterexample1038Support=
      setProjection {(0,0)} := by
    have h := congrArg Matrix.conjTranspose hPR
    simpa only [Matrix.conjTranspose_mul,(setProjection_hermitian _).eq] using h
  unfold counterexample1038Base
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,setProjection_sq,hPR,hRP]
  module

/-- The objective is the original complex matrix trace-square, not a surrogate vector norm. -/
theorem counterexample1038_purity : APPT.Quantum.purity counterexample1038=2675/1006009 := by
  unfold APPT.Quantum.purity counterexample1038
  rw [Matrix.smul_mul,Matrix.mul_smul,counterexample1038Base_sq]
  norm_num [Matrix.trace_smul,Matrix.trace_add,Matrix.trace_one,setProjection_trace,
    counterexample1038Support_card,Complex.real_smul]

/-- The exact counterexample in the paper's product-coordinate ordering. -/
theorem counterexample1038_diagonal : counterexample1038=
    Matrix.diagonal (fun p : Fin 10 × Fin 38 =>
      (((if p=(0,0) then (41:ℝ) else if 38*p.1.val+p.2.val<147 then 17 else 15)/6018:ℝ):ℂ)) := by
  ext p q
  by_cases hpq : p=q
  · subst q
    by_cases hp : p=(0,0)
    · subst p
      norm_num [counterexample1038,counterexample1038Base,setProjection,counterexample1038Support,
        Matrix.diagonal_apply,Matrix.one_apply,Complex.real_smul]
    · by_cases hs : 38*p.1.val+p.2.val<147 <;>
        norm_num [counterexample1038,counterexample1038Base,setProjection,counterexample1038Support,
          Matrix.diagonal_apply,Matrix.one_apply,Complex.real_smul,hp,hs]
  · simp [counterexample1038,counterexample1038Base,setProjection,Matrix.diagonal_apply,
      Matrix.one_apply,hpq]

/-- Full physical refutation of the proposed two-candidate purity formula at 10 by 38. -/
theorem counterexample1038_refutes_formula :
    APPT.Quantum.IsDensity counterexample1038 ∧
    APPT.Quantum.AbsolutelyPPT counterexample1038 ∧
    max ((380+8:ℝ)/(380+2)^2)
      ((380*(10-1)^2+4*10*171:ℝ)/(380*(10-1)+2*171)^2)
      < APPT.Quantum.purity counterexample1038 := by
  refine ⟨counterexample1038_isDensity,counterexample1038_absolutelyPPT,?_⟩
  rw [counterexample1038_purity]
  norm_num

end APPTReview
