import CircuitNumerical.InputAssemblyPolynomial
import Mathlib.Computability.TuringMachine.StackTuringMachine

namespace CircuitRecursion.ListAssemblyMachine

open Turing

inductive Stack where
  | left | right | work
  deriving DecidableEq
inductive Label where
  | move | restore
  deriving DecidableEq
instance : Fintype Stack := ⟨{.left,.right,.work},by intro x;cases x <;> simp⟩
instance : Fintype Label := ⟨{.move,.restore},by intro x;cases x <;> simp⟩
instance : Inhabited Label := ⟨.move⟩

abbrev Configuration (α : Type*) := TM2.Cfg (fun _ : Stack => α) Label (Option α)

def stackData {α : Type*} (as bs ws : List α) : Stack → List α
  | .left => as
  | .right => bs
  | .work => ws

@[simp] theorem stackData_left {α : Type*} (as bs ws : List α) : stackData as bs ws .left=as := rfl
@[simp] theorem stackData_right {α : Type*} (as bs ws : List α) : stackData as bs ws .right=bs := rfl
@[simp] theorem stackData_work {α : Type*} (as bs ws : List α) : stackData as bs ws .work=ws := rfl

@[simp] theorem update_stackData_left {α : Type*} (as bs ws xs : List α) :
    Function.update (stackData as bs ws) .left xs=stackData xs bs ws := by
  funext k;cases k <;> rfl
@[simp] theorem update_stackData_right {α : Type*} (as bs ws xs : List α) :
    Function.update (stackData as bs ws) .right xs=stackData as xs ws := by
  funext k;cases k <;> rfl
@[simp] theorem update_stackData_work {α : Type*} (as bs ws xs : List α) :
    Function.update (stackData as bs ws) .work xs=stackData as bs xs := by
  funext k;cases k <;> rfl

def configuration {α : Type*} (l : Option Label) (v : Option α) (as bs ws : List α) : Configuration α :=
  ⟨l,v,stackData as bs ws⟩

/-- A fixed two-label, three-stack machine. Local memory is one optional
alphabet symbol; there are no natural-number local registers or fuel input.
Every label executes at most four TM2 statement constructors. -/
def program (α : Type*) [Inhabited α] : Label → TM2.Stmt (fun _ : Stack => α) Label (Option α)
  | .move => .pop .left (fun _ x => x)
      (.branch Option.isSome
        (.push .work (fun x => x.getD default) (.goto (fun _ => .move)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .work (fun _ x => x)
      (.branch Option.isSome
        (.push .right (fun x => x.getD default) (.goto (fun _ => .restore)))
        .halt)

theorem program_supports (α : Type*) [Inhabited α] : TM2.Supports (program α) Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro q _
    cases q <;> simp [program,TM2.SupportsStmt]

theorem step_move_nil {α : Type*} [Inhabited α] (v : Option α) (bs ws : List α) :
    TM2.step (program α) (configuration (.some .move) v [] bs ws)=
      some (configuration (.some .restore) none [] bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.false_eq_true,Bool.cond_false,update_stackData_left]

theorem step_move_cons {α : Type*} [Inhabited α] (v : Option α) (a : α) (as bs ws : List α) :
    TM2.step (program α) (configuration (.some .move) v (a::as) bs ws)=
      some (configuration (.some .move) (some a) as bs (a::ws)) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,stackData_work,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some,update_stackData_left,update_stackData_work]

theorem step_restore_nil {α : Type*} [Inhabited α] (v : Option α) (as bs : List α) :
    TM2.step (program α) (configuration (.some .restore) v as bs [])=
      some (configuration none none as bs []) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_work,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.false_eq_true,Bool.cond_false,update_stackData_work]

theorem step_restore_cons {α : Type*} [Inhabited α] (v : Option α) (a : α) (as bs ws : List α) :
    TM2.step (program α) (configuration (.some .restore) v as bs (a::ws))=
      some (configuration (.some .restore) (some a) as (a::bs) ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_work,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,Option.getD_some,update_stackData_work,update_stackData_right]

theorem step_halt {α : Type*} [Inhabited α] (v : Option α) (as bs ws : List α) :
    TM2.step (program α) (configuration none v as bs ws)=none := rfl

end CircuitRecursion.ListAssemblyMachine
