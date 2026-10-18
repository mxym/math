import CircuitRecursion.SU2Conjugacy

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

def axisX (c s : ℝ) (hcs : c^2+s^2=1) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  quaternionSU2 (c : ℂ) (Complex.I*(s : ℂ)) (by
    simpa [Complex.normSq_mul,Complex.normSq_ofReal,pow_two] using hcs)

def axisY (c s : ℝ) (hcs : c^2+s^2=1) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  quaternionSU2 (c : ℂ) (s : ℂ) (by
    simpa [Complex.normSq_ofReal,pow_two] using hcs)

def su2Commutator (A B : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ := A*B*A⁻¹*B⁻¹

theorem su2Commutator_unitary (A B : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    su2AsUnitary (su2Commutator A B)=unitaryCommutator (su2AsUnitary A) (su2AsUnitary B) := rfl

theorem unitaryCommutator_conjugate (P A B : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryCommutator (P*A*star P) (P*B*star P)=P*unitaryCommutator A B*star P := by
  simp [unitaryCommutator,Unitary.star_eq_inv,mul_assoc]

theorem axisCommutator_scalar (c s : ℝ) (hcs : c^2+s^2=1) :
    ((su2Commutator (axisX c s hcs) (axisY c s hcs)).val 0 0).re=1-2*s^4 := by
  change ((((quaternionMatrix (c : ℂ) (Complex.I*(s : ℂ))*quaternionMatrix (c : ℂ) (s : ℂ))*
    (quaternionMatrix (c : ℂ) (Complex.I*(s : ℂ)))ᴴ)*
      (quaternionMatrix (c : ℂ) (s : ℂ))ᴴ) 0 0).re = _
  simp [quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
    Matrix.vecMul,Matrix.mulVec,dotProduct,Complex.mul_re,Complex.mul_im]
  nlinarith [sq_nonneg (c^2+s^2-1)]

theorem axisX_distance (c s : ℝ) (hcs : c^2+s^2=1) :
    unitaryDistance (su2AsUnitary (axisX c s hcs)) 1^2=2-2*c := by
  rw [su2_distance_square]
  rfl

theorem axisY_distance (c s : ℝ) (hcs : c^2+s^2=1) :
    unitaryDistance (su2AsUnitary (axisY c s hcs)) 1^2=2-2*c := by
  rw [su2_distance_square]
  rfl

/-- Every actual SU(2) matrix is a balanced group commutator. The factors
are constructed from square-root plane rotations and an internally proved
unitary conjugacy; their near-identity bounds are part of the conclusion. -/
theorem su2_balanced_commutator (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ A B : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      U=su2Commutator A B ∧
      unitaryDistance (su2AsUnitary A) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) ∧
      unitaryDistance (su2AsUnitary B) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) := by
  let r := (U.val 0 0).re
  let t := Real.sqrt ((1-r)/2)
  let s := Real.sqrt t
  let c := Real.sqrt (1-s^2)
  let d := unitaryDistance (su2AsUnitary U) 1
  have hr := su2_scalarPart_bounds U
  have ht0 : 0≤t := Real.sqrt_nonneg _
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hc0 : 0≤c := Real.sqrt_nonneg _
  have hd0 : 0≤d := unitaryDistance_nonneg _ _
  have ht2 : t^2=(1-r)/2 := Real.sq_sqrt (by dsimp [r]; linarith [hr.2])
  have hs2 : s^2=t := Real.sq_sqrt ht0
  have hs4 : s^4=(1-r)/2 := by nlinarith
  have ht1 : t≤1 := by dsimp [r] at ht2; nlinarith [hr.1]
  have hs1 : s^2≤1 := by linarith
  have hc2 : c^2=1-s^2 := Real.sq_sqrt (by linarith)
  have hcs : c^2+s^2=1 := by linarith
  have hc1 : c≤1 := by nlinarith [sq_nonneg s]
  have hcc : c*c≤c := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have hd2 : d^2=2-2*r := su2_distance_square U
  have hsd : 2*s^2=d := by
    apply (sq_eq_sq₀ (by positivity) hd0).mp
    nlinarith
  let X := axisX c s hcs
  let Y := axisY c s hcs
  let W := su2Commutator X Y
  have hscalar : (U.val 0 0).re=(W.val 0 0).re := by
    rw [axisCommutator_scalar]
    dsimp [r] at hs4
    linarith
  obtain ⟨P,hP⟩ := su2_sameScalar_conjugate U W hscalar
  have hX : unitaryDistance (su2AsUnitary X) 1≤Real.sqrt d := by
    have hn := axisX_distance c s hcs
    have hroot := Real.sq_sqrt hd0
    have hn0 := unitaryDistance_nonneg (su2AsUnitary X) 1
    have hroot0 := Real.sqrt_nonneg d
    nlinarith
  have hY : unitaryDistance (su2AsUnitary Y) 1≤Real.sqrt d := by
    have hn := axisY_distance c s hcs
    have hroot := Real.sq_sqrt hd0
    have hn0 := unitaryDistance_nonneg (su2AsUnitary Y) 1
    have hroot0 := Real.sqrt_nonneg d
    nlinarith
  let A := su2Conjugate P X
  let B := su2Conjugate P Y
  have hcomm : su2AsUnitary (su2Commutator A B)=P*su2AsUnitary W*star P := by
    rw [su2Commutator_unitary,su2Conjugate_unitary,su2Conjugate_unitary,
      unitaryCommutator_conjugate,← su2Commutator_unitary]
  refine ⟨A,B,?_,?_,?_⟩
  · apply Subtype.ext
    exact hP.trans (congrArg Subtype.val hcomm).symm
  · rw [su2Conjugate_unitary,unitaryDistance_conjugate_one]
    exact hX
  · rw [su2Conjugate_unitary,unitaryDistance_conjugate_one]
    exact hY

theorem su2_near_identity_commutator (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (ε : ℝ) (hU : unitaryDistance (su2AsUnitary U) 1≤ε) :
    ∃ A B : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      U=su2Commutator A B ∧
      unitaryDistance (su2AsUnitary A) 1≤Real.sqrt ε ∧
      unitaryDistance (su2AsUnitary B) 1≤Real.sqrt ε := by
  obtain ⟨A,B,he,hA,hB⟩ := su2_balanced_commutator U
  exact ⟨A,B,he,hA.trans (Real.sqrt_le_sqrt hU),hB.trans (Real.sqrt_le_sqrt hU)⟩

end CircuitRecursion
