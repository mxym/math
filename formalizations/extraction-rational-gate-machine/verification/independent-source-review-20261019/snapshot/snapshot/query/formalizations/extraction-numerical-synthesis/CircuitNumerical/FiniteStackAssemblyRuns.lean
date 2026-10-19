import CircuitNumerical.FiniteStackAssembly
import Mathlib.Computability.StateTransition

namespace CircuitRecursion.ListAssemblyMachine

open Turing

set_option maxHeartbeats 1500000

/-- A lifted official TM2 transition; the iteration index in the proofs is
an external time bound, not a Nat variable or fuel in the finite machine. -/
def advance (α : Type*) [Inhabited α] : Option (Configuration α) → Option (Configuration α) :=
  fun c => c.bind (TM2.step (program α))

theorem advance_some {α : Type*} [Inhabited α] (c : Configuration α) :
    advance α (some c)=TM2.step (program α) c := rfl

theorem move_iterate {α : Type*} [Inhabited α] (v : Option α) (as bs ws : List α) :
    (advance α)^[as.length+1] (some (configuration (.some .move) v as bs ws))=
      some (configuration (.some .restore) none [] bs (as.reverse++ws)) := by
  induction as generalizing v ws with
  | nil =>
    change TM2.step (program α) (configuration (.some .move) v [] bs ws)=_
    exact step_move_nil v bs ws
  | cons a as ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    rw [advance_some,step_move_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem restore_iterate {α : Type*} [Inhabited α] (v : Option α) (as bs ws : List α) :
    (advance α)^[ws.length+1] (some (configuration (.some .restore) v as bs ws))=
      some (configuration none none as (ws.reverse++bs) []) := by
  induction ws generalizing v bs with
  | nil =>
    change TM2.step (program α) (configuration (.some .restore) v as bs [])=_
    exact step_restore_nil v as bs
  | cons a ws ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    rw [advance_some,step_restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem append_iterate {α : Type*} [Inhabited α] (as bs : List α) :
    (advance α)^[2*as.length+2] (some (configuration (.some .move) none as bs []))=
      some (configuration none none [] (as++bs) []) := by
  rw [show 2*as.length+2=(as.length+1)+(as.length+1) by omega,Function.iterate_add_apply,move_iterate]
  simp only [List.append_nil]
  have h:=restore_iterate (α:=α) none [] bs as.reverse
  simpa only [List.length_reverse,List.reverse_reverse] using h

/-- An actual run of the official TM2 step function, with an internally
proved exact transition count. Its machine has finite state/local memory
whenever the alphabet is finite. No caller time certificate is supplied. -/
def appendRun {α : Type*} [Inhabited α] (as bs : List α) :
    StateTransition.EvalsToInTime (TM2.step (program α))
      (configuration (.some .move) none as bs [])
      (some (configuration none none [] (as++bs) [])) (2*as.length+2) :=
  ⟨⟨2*as.length+2,append_iterate as bs⟩,le_refl _⟩

theorem appendRun_steps {α : Type*} [Inhabited α] (as bs : List α) :
    (appendRun as bs).steps=2*as.length+2 := rfl

theorem append_terminal {α : Type*} [Inhabited α] (as bs : List α) :
    TM2.step (program α) (configuration none none [] (as++bs) [])=none := rfl

theorem append_output {α : Type*} [Inhabited α] (as bs : List α) :
    (configuration (α:=α) none none [] (as++bs) []).stk .right=(listAppendProgram as bs).value :=
  (listAppendProgram_value as bs).symm

/-- A proved operational bridge to the existing source list-copy fee.
It concerns this finite stack machine, not all costs of the compiler. -/
theorem appendRun_steps_le_source_actions {α : Type*} [Inhabited α] (as bs : List α) :
    (appendRun as bs).steps≤2*(listAppendProgram as bs).trace.actions := by
  rw [appendRun_steps,listAppendProgram_actions]
  omega

end CircuitRecursion.ListAssemblyMachine
