import CircuitCompletion.Semantics
import Extraction.KrausCompletion

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace CircuitCompletion

/-- Literal plane rotation coefficients; the action outside this two-dimensional
matrix will be the identity under embedPlane. -/
def rotationMatrix (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c:ℂ),(s:ℂ);-(s:ℂ),(c:ℂ)]

noncomputable def rotationUnitary (c s : ℝ) (h : c*c+s*s=1) : Matrix.unitaryGroup (Fin 2) ℂ := by
  refine ⟨rotationMatrix c s,Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  have hc : (c:ℂ)*(c:ℂ)+(s:ℂ)*(s:ℂ)=1 := by exact_mod_cast h
  change (rotationMatrix c s)ᴴ*rotationMatrix c s=1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
  · exact hc
  · ring
  · ring
  · simpa only [neg_mul_neg,add_comm] using hc

noncomputable def mergeRotation (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Matrix.unitaryGroup (Fin 2) ℂ := by
  by_cases h : a+b=0
  · exact 1
  · have hp : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    have hr : Real.sqrt (a+b)≠0 := (Real.sqrt_pos.mpr hp).ne'
    refine rotationUnitary (Real.sqrt a/Real.sqrt (a+b)) (Real.sqrt b/Real.sqrt (a+b)) ?_
    field_simp
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hp.le]

/-- The actual algebraic Givens operation combines two nonnegative masses,
including zero coefficients, into one coordinate with no state-dependent choice. -/
theorem mergeRotation_action (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (mergeRotation a b ha hb : Matrix (Fin 2) (Fin 2) ℂ)*ᵥ
      ![(Real.sqrt a:ℂ),(Real.sqrt b:ℂ)]=![(Real.sqrt (a+b):ℂ),0] := by
  by_cases h : a+b=0
  · have hA : a=0 := by linarith
    have hB : b=0 := by linarith
    simp [mergeRotation,h,hA,hB]
  · have hp : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    have hr : Real.sqrt (a+b)≠0 := (Real.sqrt_pos.mpr hp).ne'
    have hre : (Real.sqrt (a+b):ℂ)≠0 := by exact_mod_cast hr
    ext i
    fin_cases i <;> simp [mergeRotation,h,rotationUnitary,rotationMatrix,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two]
    · have he : Real.sqrt a/Real.sqrt (a+b)*Real.sqrt a+
          Real.sqrt b/Real.sqrt (a+b)*Real.sqrt b=Real.sqrt (a+b) := by
        field_simp
        nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hp.le]
      exact_mod_cast he
    · field_simp
      ring

/-- Place a literal two-dimensional unitary in an original-space isometric
plane, with the identity on the orthogonal complement. No unitary extension
existence theorem or ancillary register is used. -/
noncomputable def embedPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι (Fin 2) ℂ) (hE : Eᴴ*E=1) (G : Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix.unitaryGroup ι ℂ := by
  let Q := 1-E*Eᴴ
  have hQ : Qᴴ=Q := Extraction.isometry_complement_hermitian E
  have hQQ : Q*Q=Q := Extraction.isometry_complement_square E hE
  have hQE : Q*E=0 := by simp only [Q,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,hE,Matrix.mul_one,sub_self]
  have hEQ : Eᴴ*Q=0 := by
    have h := congrArg Matrix.conjTranspose hQE
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_zero,hQ,Matrix.conjTranspose_conjTranspose] using h
  let A := E*(G : Matrix (Fin 2) (Fin 2) ℂ)*Eᴴ
  have hAA : Aᴴ*A=E*Eᴴ := by
    dsimp only [A]
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ,hE,Matrix.one_mul]
    rw [← Matrix.mul_assoc (G : Matrix (Fin 2) (Fin 2) ℂ)ᴴ]
    have hG : (G : Matrix (Fin 2) (Fin 2) ℂ)ᴴ*G=1 := by
      simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self G
    rw [hG,Matrix.one_mul]
  have hAQ : Aᴴ*Q=0 := by
    dsimp only [A]
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
    rw [hEQ,Matrix.mul_zero,Matrix.mul_zero]
  have hQA : Q*A=0 := by
    dsimp only [A]
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hQE,Matrix.zero_mul,Matrix.zero_mul]
  refine ⟨A+Q,Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (A+Q)ᴴ*(A+Q)=1
  rw [Matrix.conjTranspose_add,hQ,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,hAA,hAQ,hQA,hQQ]
  dsimp only [Q]
  abel

theorem embedPlane_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι (Fin 2) ℂ) (hE : Eᴴ*E=1) (G : Matrix.unitaryGroup (Fin 2) ℂ)
    (v : Fin 2 → ℂ) :
    (embedPlane E hE G : Matrix ι ι ℂ)*ᵥ(E*ᵥv)=
      E*ᵥ((G : Matrix (Fin 2) (Fin 2) ℂ)*ᵥv) := by
  have h : (embedPlane E hE G : Matrix ι ι ℂ)*E=E*(G : Matrix (Fin 2) (Fin 2) ℂ) := by
    change (E*(G : Matrix (Fin 2) (Fin 2) ℂ)*Eᴴ+(1-E*Eᴴ))*E=_
    simp only [Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,hE,
      Matrix.mul_one,sub_self,add_zero]
  rw [Matrix.mulVec_mulVec,h,← Matrix.mulVec_mulVec]

end CircuitCompletion
