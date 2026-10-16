import CircuitCompletion.AdjacentSwap

open scoped BigOperators
open Matrix
namespace CircuitCompletion

noncomputable def yBasis : Matrix.unitaryGroup Bool ℂ :=
  diagonalUnitary (fun b => if b then Complex.I else 1)
    (fun b => by cases b <;> norm_num)*hadamard

theorem yBasis_entry (b c : Bool) :
    (yBasis : Matrix Bool Bool ℂ) b c=
      (if b then Complex.I else 1)*(invSqrtTwo : ℂ)*(if b && c then -1 else 1) := by
  simp only [yBasis,Matrix.UnitaryGroup.mul_val,diagonalUnitary,Matrix.diagonal_mul,
    hadamard_entry,mul_assoc]

theorem yBasis_star_entry (b c : Bool) :
    (star yBasis : Matrix.unitaryGroup Bool ℂ) b c=
      (if c then -Complex.I else 1)*(invSqrtTwo : ℂ)*(if c && b then -1 else 1) := by
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    yBasis_entry]
  cases b <;> cases c <;> simp

theorem complexPhase_trig (θ : ℝ) :
    complexPhase θ=(Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I := by
  simp [complexPhase,Complex.exp_mul_I]

/-- A controlled real Givens rotation obtained by two literal selected phases
and two original-wire basis changes. No many-controlled gate is primitive. -/
noncomputable def adjacentRotationWord {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (θ : ℝ) : Circuit n :=
  [Gate.single t (star yBasis)]++
    selectedPhaseWord hn (Function.update x t false) θ++
    selectedPhaseWord hn (Function.update x t true) (-θ)++[Gate.single t yBasis]

theorem adjacentRotationWord_action {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (θ : ℝ) (v : Bits n → ℂ) :
    run (adjacentRotationWord hn t x θ) v=fun w =>
      if sameOutside t w x then
        if w t then -(Real.sin θ : ℂ)*v (Function.update w t false)+
          (Real.cos θ : ℂ)*v (Function.update w t true)
        else (Real.cos θ : ℂ)*v (Function.update w t false)+
          (Real.sin θ : ℂ)*v (Function.update w t true)
      else v w := by
  classical
  simp only [adjacentRotationWord,run_append,run_single,selectedPhaseWord_action]
  funext w
  simp only [Fintype.sum_bool,yBasis_entry,yBasis_star_entry]
  have hc : (invSqrtTwo : ℂ)*(invSqrtTwo : ℂ)+(invSqrtTwo : ℂ)*(invSqrtTwo : ℂ)=1 := by
    exact_mod_cast invSqrtTwo_square
  have hc2 : (invSqrtTwo : ℂ)^2=(1/2 : ℂ) := by linear_combination hc/2
  have hup : Function.update w t (w t)=w := Function.update_eq_self t w
  by_cases h : sameOutside t w x <;> cases hb : w t
  all_goals
    simp only [hb] at hup
    simp [update_eq_update_iff,h,hb,Function.update_idem,complexPhase_zero,
      complexPhase_trig,Real.cos_neg,Real.sin_neg]
  all_goals try rw [hup]
  all_goals ring_nf
  all_goals rw [hc2]
  all_goals norm_num
  all_goals ring

theorem adjacentRotationWord_length {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) (θ : ℝ) :
    (adjacentRotationWord hn t x θ).length≤2*(2^n*(2*n+1))+2 := by
  have h0 := selectedPhaseWord_length hn (Function.update x t false) θ
  have h1 := selectedPhaseWord_length hn (Function.update x t true) (-θ)
  simp only [adjacentRotationWord,List.length_append,List.length_singleton]
  omega

end CircuitCompletion
