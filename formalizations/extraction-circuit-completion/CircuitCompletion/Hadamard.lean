import CircuitCompletion.Givens
import CircuitCompletion.Pauli

open scoped BigOperators
open Matrix
namespace CircuitCompletion

noncomputable def invSqrtTwo : ℝ := Real.sqrt 2/2

theorem invSqrtTwo_square : invSqrtTwo*invSqrtTwo+invSqrtTwo*invSqrtTwo=1 := by
  unfold invSqrtTwo
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]

noncomputable def hadamard : Matrix.unitaryGroup Bool ℂ :=
  reindexUnitary finTwoEquiv
    ((diagonalUnitary (fun i : Fin 2 => if i=0 then (1 : ℂ) else -1)
      (fun i => by fin_cases i <;> norm_num))*
      rotationUnitary invSqrtTwo invSqrtTwo invSqrtTwo_square)

theorem hadamard_entry (b c : Bool) :
    (hadamard : Matrix Bool Bool ℂ) b c=
      (invSqrtTwo : ℂ)*(if b && c then -1 else 1) := by
  cases b <;> cases c <;>
    norm_num [hadamard,reindexUnitary,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,
      diagonalUnitary,Matrix.mul_apply,Fin.sum_univ_two,rotationUnitary,rotationMatrix,finTwoEquiv]

theorem hadamard_star : star hadamard=hadamard := by
  apply Subtype.ext
  ext b c
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    hadamard_entry]
  cases b <;> cases c <;> simp

theorem complexPhase_zero : complexPhase 0=1 := by simp [complexPhase]

theorem complexPhase_pi : complexPhase Real.pi=-1 := Complex.exp_pi_mul_I

end CircuitCompletion
