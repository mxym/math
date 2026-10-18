import CircuitCompletion.Hadamard
import CircuitCompletion.LocalAction
import CircuitCompletion.SelectedPhase

open scoped BigOperators
open Matrix
namespace CircuitCompletion

def sameOutside {n : ℕ} (t : Fin n) (w x : Bits n) : Prop :=
  ∀ j,j≠t → w j=x j

instance {n : ℕ} (t : Fin n) (w x : Bits n) : Decidable (sameOutside t w x) :=
  inferInstanceAs (Decidable (∀ j,j≠t → w j=x j))

theorem sameOutside_update {n : ℕ} (t : Fin n) (w x : Bits n) (b : Bool) :
    sameOutside t (Function.update w t b) x ↔ sameOutside t w x := by
  constructor <;> intro h j hj
  · simpa [Function.update_of_ne hj] using h j hj
  · simpa [Function.update_of_ne hj] using h j hj

theorem update_eq_update_iff {n : ℕ} (t : Fin n) (w x : Bits n) (b c : Bool) :
    Function.update w t b=Function.update x t c ↔ b=c ∧ sameOutside t w x := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · have ht := congrFun h t
      simpa using ht
    · intro j hj
      have hj' := congrFun h j
      simpa [Function.update_of_ne hj] using hj'
  · rintro ⟨rfl,h⟩
    funext j
    by_cases hj : j=t
    · subst j;simp
    · simp [Function.update_of_ne hj,h j hj]

theorem run_single {n : ℕ} (t : Fin n) (U : Matrix.unitaryGroup Bool ℂ)
    (v : Bits n → ℂ) :
    run [Gate.single t U] v=fun w => ∑ b : Bool,(U : Matrix Bool Bool ℂ) (w t) b*
      v (Function.update w t b) := by
  funext w
  simp only [run,denote,one_mul]
  exact singleWire_action t U v w

theorem run_hadamard {n : ℕ} (t : Fin n) (v : Bits n → ℂ) :
    run [Gate.single t hadamard] v=fun w =>
      (invSqrtTwo : ℂ)*(if w t then -v (Function.update w t true) else v (Function.update w t true))+
      (invSqrtTwo : ℂ)*v (Function.update w t false) := by
  rw [run_single]
  funext w
  rw [Fintype.sum_bool]
  simp only [hadamard_entry,Bool.and_true,Bool.and_false,Bool.false_eq_true,if_false,
    mul_one]
  cases w t <;> simp

/-- Swap two selected computational strings differing in one existing wire.
All other strings are fixed; every gate in this word is primitive. -/
noncomputable def adjacentSwapWord {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) : Circuit n :=
  [Gate.single t hadamard]++selectedPhaseWord hn (Function.update x t true) Real.pi++
    [Gate.single t hadamard]

theorem adjacentSwapWord_action {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (v : Bits n → ℂ) :
    run (adjacentSwapWord hn t x) v=fun w =>
      if sameOutside t w x then v (Function.update w t (!w t)) else v w := by
  classical
  simp only [adjacentSwapWord,run_append,run_hadamard,selectedPhaseWord_action]
  funext w
  have hc : (invSqrtTwo : ℂ)*(invSqrtTwo : ℂ)+(invSqrtTwo : ℂ)*(invSqrtTwo : ℂ)=1 := by
    exact_mod_cast invSqrtTwo_square
  have hc2 : (invSqrtTwo : ℂ)^2=(1/2 : ℂ) := by
    linear_combination hc/2
  have hup : Function.update w t (w t)=w := Function.update_eq_self t w
  by_cases h : sameOutside t w x <;> cases hb : w t
  all_goals
    simp only [hb] at hup
    simp [update_eq_update_iff,h,hb,Function.update_idem,
      complexPhase_zero,complexPhase_pi]
  all_goals try rw [hup]
  all_goals ring_nf
  all_goals rw [hc2]
  all_goals ring

theorem adjacentSwapWord_length {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) :
    (adjacentSwapWord hn t x).length≤2^n*(2*n+1)+2 := by
  have h := selectedPhaseWord_length hn (Function.update x t true) Real.pi
  simpa only [adjacentSwapWord,List.length_append,List.length_singleton] using
    (show 1+(selectedPhaseWord hn (Function.update x t true) Real.pi).length+1≤
      2^n*(2*n+1)+2 by omega)

end CircuitCompletion
