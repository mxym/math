import CircuitNumerical.FiniteStackAssemblyRuns

namespace CircuitRecursion.ListAssemblyMachine

open Turing

/-- f is a fixed alphabet transition table. For a finite alphabet it is a
finite machine table, not an arbitrary provider procedure invoked at runtime. -/
def reverseProgram (α : Type*) [Inhabited α] (f : α → α) :
    Label → TM2.Stmt (fun _ : Stack => α) Label (Option α)
  | .move => .pop .left (fun _ x => x)
      (.branch Option.isSome
        (.push .right (fun x => f (x.getD default)) (.goto (fun _ => .move)))
        .halt)
  | .restore => .halt

theorem reverseProgram_supports (α : Type*) [Inhabited α] (f : α → α) :
    TM2.Supports (reverseProgram α f) Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro q _
    cases q <;> simp [reverseProgram,TM2.SupportsStmt]

theorem reverse_step_nil {α : Type*} [Inhabited α] (f : α → α) (v : Option α) (bs ws : List α) :
    TM2.step (reverseProgram α f) (configuration (.some .move) v [] bs ws)=
      some (configuration none none [] bs ws) := by
  simp only [configuration,TM2.step,reverseProgram,TM2.stepAux,stackData_left,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_left]

theorem reverse_step_cons {α : Type*} [Inhabited α] (f : α → α) (v : Option α) (a : α) (as bs ws : List α) :
    TM2.step (reverseProgram α f) (configuration (.some .move) v (a::as) bs ws)=
      some (configuration (.some .move) (some a) as (f a::bs) ws) := by
  simp only [configuration,TM2.step,reverseProgram,TM2.stepAux,stackData_left,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some,update_stackData_left,update_stackData_right]

def reverseAdvance (α : Type*) [Inhabited α] (f : α → α) :
    Option (Configuration α) → Option (Configuration α) := fun c => c.bind (TM2.step (reverseProgram α f))

theorem reverse_iterate {α : Type*} [Inhabited α] (f : α → α) (v : Option α) (as bs ws : List α) :
    (reverseAdvance α f)^[as.length+1] (some (configuration (.some .move) v as bs ws))=
      some (configuration none none [] (as.reverse.map f++bs) ws) := by
  induction as generalizing v bs with
  | nil =>
    change TM2.step (reverseProgram α f) (configuration (.some .move) v [] bs ws)=_
    exact reverse_step_nil f v bs ws
  | cons a as ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (reverseAdvance α f)^[as.length+1]
      (TM2.step (reverseProgram α f) (configuration (.some .move) v (a::as) bs ws))=_
    rw [reverse_step_cons,ih]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
      List.cons_append,List.nil_append]

def reverseRun {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    StateTransition.EvalsToInTime (TM2.step (reverseProgram α f))
      (configuration (.some .move) none as bs ws)
      (some (configuration none none [] (as.reverse.map f++bs) ws)) (as.length+1) :=
  ⟨⟨as.length+1,reverse_iterate f none as bs ws⟩,le_refl _⟩

theorem reverseRun_steps {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    (reverseRun f as bs ws).steps=as.length+1 := rfl

theorem reverse_terminal {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    TM2.step (reverseProgram α f) (configuration none none [] (as.reverse.map f++bs) ws)=none := rfl

theorem reverse_output {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    (configuration (α:=α) none none [] (as.reverse.map f++bs) ws).stk .right=
      (listReverseMapIntoProgram f as bs).value :=
  (listReverseMapIntoProgram_value f as bs).symm

theorem reverseRun_steps_le_source_actions {α : Type*} [Inhabited α] (f : α → α) (as bs ws : List α) :
    (reverseRun f as bs ws).steps≤(listReverseMapIntoProgram f as bs).trace.actions := by
  rw [reverseRun_steps,listReverseMapIntoProgram_actions]
  omega

/-- This is a finite-alphabet implementation of the instruction inverse
backend for a fixed finite inverse-label table. -/
def instructionInverseRun {m : ℕ} [NeZero m] (inverseLabel : Fin m → Fin m) (word : List (Fin m)) :
    StateTransition.EvalsToInTime (TM2.step (reverseProgram (Fin m) inverseLabel))
      (configuration (.some .move) none word [] [])
      (some (configuration none none [] (instructionInverse inverseLabel word) [])) (word.length+1) :=
  ⟨⟨word.length+1,by
    change (reverseAdvance (Fin m) inverseLabel)^[word.length+1]
      (some (configuration (.some .move) none word [] []))=_
    simpa only [instructionInverse,List.append_nil] using reverse_iterate inverseLabel none word [] []⟩,le_refl _⟩

theorem instructionInverseRun_steps {m : ℕ} [NeZero m] (inverseLabel : Fin m → Fin m) (word : List (Fin m)) :
    (instructionInverseRun inverseLabel word).steps=word.length+1 := rfl

end CircuitRecursion.ListAssemblyMachine
