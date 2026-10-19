import CircuitNumerical.PacketRecordSemantics

namespace CircuitRecursion.PacketMasterMachine

open Turing PacketFraming

/-- Three working stacks plus a fourth physical cache master. -/
abbrev Stack := ListAssemblyMachine.Stack ⊕ Unit

def stackData (index scratch cache master : List Symbol) : Stack → List Symbol
  | .inl .left => index
  | .inl .right => scratch
  | .inl .work => cache
  | .inr _ => master

abbrev Configuration (Λ : Type*) := TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)

def configuration {Λ : Type*} (l : Option Λ) (v : Option Symbol)
    (index scratch cache master : List Symbol) : Configuration Λ :=
  ⟨l,v,stackData index scratch cache master⟩

theorem update_scratch (i s c m xs : List Symbol) :
    Function.update (stackData i s c m) (.inl .right) xs=stackData i xs c m := by
  funext k
  cases k with
  | inl k => cases k <;> simp [stackData,Function.update]
  | inr k => simp [stackData,Function.update]

theorem update_cache (i s c m xs : List Symbol) :
    Function.update (stackData i s c m) (.inl .work) xs=stackData i s xs m := by
  funext k
  cases k with
  | inl k => cases k <;> simp [stackData,Function.update]
  | inr k => simp [stackData,Function.update]

theorem update_master (i s c m xs : List Symbol) :
    Function.update (stackData i s c m) (.inr ()) xs=stackData i s c xs := by
  funext k
  cases k with
  | inl k => cases k <;> simp [stackData,Function.update]
  | inr k => cases k;simp [stackData,Function.update]

inductive CloneLabel where
  | move | restore
  deriving DecidableEq
instance : Fintype CloneLabel := ⟨{.move,.restore},by intro x;cases x <;> simp⟩
instance : Inhabited CloneLabel := ⟨.move⟩

/-- Drain the master into scratch, then restore every concrete symbol onto
both the master and working cache. No packet is an atomic symbol and no
persistent sharing or host copying operation is used. -/
def cloneProgram : CloneLabel → TM2.Stmt (fun _ : Stack => Symbol) CloneLabel (Option Symbol)
  | .move => .pop (.inr ()) (fun _ x => x)
      (.branch Option.isSome
        (.push (.inl .right) (fun x => x.getD default) (.goto (fun _ => .move)))
        (.goto (fun _ => .restore)))
  | .restore => .pop (.inl .right) (fun _ x => x)
      (.branch Option.isSome
        (.push (.inr ()) (fun x => x.getD default)
          (.push (.inl .work) (fun x => x.getD default) (.goto (fun _ => .restore))))
        .halt)

def cloneAdvance : Option (Configuration CloneLabel) → Option (Configuration CloneLabel) :=
  fun c => c.bind (TM2.step cloneProgram)

theorem clone_move_nil (v : Option Symbol) (i s c : List Symbol) :
    TM2.step cloneProgram (configuration (some .move) v i s c [])=
      some (configuration (some .restore) none i s c []) := by
  simp only [configuration,TM2.step,cloneProgram,TM2.stepAux,stackData,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_master]

theorem clone_move_cons (v : Option Symbol) (a : Symbol) (i s c m : List Symbol) :
    TM2.step cloneProgram (configuration (some .move) v i s c (a::m))=
      some (configuration (some .move) (some a) i (a::s) c m) := by
  simp only [configuration,TM2.step,cloneProgram,TM2.stepAux,stackData,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_master,update_scratch]

theorem clone_restore_nil (v : Option Symbol) (i c m : List Symbol) :
    TM2.step cloneProgram (configuration (some .restore) v i [] c m)=
      some (configuration none none i [] c m) := by
  simp only [configuration,TM2.step,cloneProgram,TM2.stepAux,stackData,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_scratch]

theorem clone_restore_cons (v : Option Symbol) (a : Symbol) (i s c m : List Symbol) :
    TM2.step cloneProgram (configuration (some .restore) v i (a::s) c m)=
      some (configuration (some .restore) (some a) i s (a::c) (a::m)) := by
  simp only [configuration,TM2.step,cloneProgram,TM2.stepAux,stackData,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_scratch,update_master,update_cache]

theorem clone_move_iterate (v : Option Symbol) (i s c m : List Symbol) :
    cloneAdvance^[m.length+1] (some (configuration (some .move) v i s c m))=
      some (configuration (some .restore) none i (m.reverse++s) c []) := by
  induction m generalizing v s with
  | nil => exact clone_move_nil v i s c
  | cons a m ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change cloneAdvance^[m.length+1] (TM2.step cloneProgram
      (configuration (some .move) v i s c (a::m)))=_
    rw [clone_move_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem clone_restore_iterate (v : Option Symbol) (i s c m : List Symbol) :
    cloneAdvance^[s.length+1] (some (configuration (some .restore) v i s c m))=
      some (configuration none none i [] (s.reverse++c) (s.reverse++m)) := by
  induction s generalizing v c m with
  | nil => exact clone_restore_nil v i c m
  | cons a s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change cloneAdvance^[s.length+1] (TM2.step cloneProgram
      (configuration (some .restore) v i (a::s) c m))=_
    rw [clone_restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem clone_iterate (i m : List Symbol) :
    cloneAdvance^[2*m.length+2] (some (configuration (some .move) none i [] [] m))=
      some (configuration none none i [] m m) := by
  rw [show 2*m.length+2=(m.reverse.length+1)+(m.length+1) by simp;omega,
    Function.iterate_add_apply,clone_move_iterate]
  simp only [List.append_nil]
  rw [clone_restore_iterate]
  simp only [List.reverse_reverse,List.append_nil]

/-- The exact official transition count charges both passes and their EOF
checks. The cache length is a proof-side time index, never machine data. -/
def cloneRun (i m : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step cloneProgram)
      (configuration (some .move) none i [] [] m)
      (some (configuration none none i [] m m)) (2*m.length+2) :=
  ⟨⟨2*m.length+2,clone_iterate i m⟩,le_rfl⟩

theorem cloneRun_steps (i m : List Symbol) : (cloneRun i m).steps=2*m.length+2 := rfl

theorem clone_halt (v : Option Symbol) (i s c m : List Symbol) :
    TM2.step cloneProgram (configuration none v i s c m)=none := rfl

theorem clone_mem_eval (i m : List Symbol) : configuration none none i [] m m∈
    StateTransition.eval (TM2.step cloneProgram) (configuration (some .move) none i [] [] m) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (cloneRun i m).toEvalsTo (clone_halt _ _ _ _ _)

theorem clone_supports : TM2.Supports cloneProgram Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem clone_running_control_card : Fintype.card (CloneLabel×Option Symbol)=10 := by decide

theorem clone_statement_depth (q : CloneLabel) : ListAssemblyMachine.statementDepth (cloneProgram q)≤5 := by
  cases q <;> simp only [cloneProgram,ListAssemblyMachine.statementDepth] <;> omega

end CircuitRecursion.PacketMasterMachine
