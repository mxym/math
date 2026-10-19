import CircuitNumerical.BinaryCounterPredecessor

namespace CircuitRecursion.BinaryCounterMachine

open Turing ListAssemblyMachine

inductive Label where
  | borrow | drain | restore | clear
  deriving DecidableEq
instance : Fintype Label := ⟨{.borrow,.drain,.restore,.clear},by intro x;cases x <;> simp⟩
instance : Inhabited Label := ⟨.borrow⟩

abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def configuration (l : Option Label) (v : Option Bool) (as bs ws : List Bool) : Configuration :=
  ⟨l,v,stackData as bs ws⟩

/-- A finite borrow/transfer/restore/underflow machine for an LSB counter.
The third stack is untouched, so an enclosing program can retain its data.
No Nat values or arithmetic occur in any transition. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .borrow => .pop .left (fun _ x => x)
      (.branch Option.isSome
        (.branch (fun x => x.getD false)
          (.peek .left (fun _ x => x)
            (.branch Option.isSome
              (.push .right (fun _ => false) (.goto (fun _ => .drain)))
              (.goto (fun _ => .restore))))
          (.push .right (fun _ => true) (.goto (fun _ => .borrow))))
        (.goto (fun _ => .clear)))
  | .drain => .pop .left (fun _ x => x)
      (.branch Option.isSome
        (.push .right (fun x => x.getD false) (.goto (fun _ => .drain)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .right (fun _ x => x)
      (.branch Option.isSome
        (.push .left (fun x => x.getD false) (.goto (fun _ => .restore)))
        .halt)
  | .clear => .pop .right (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .clear)) .halt)

theorem program_supports : TM2.Supports program Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro q _
    cases q <;> simp [program,TM2.SupportsStmt]

theorem borrow_nil (v : Option Bool) (bs ws : List Bool) :
    TM2.step program (configuration (.some .borrow) v [] bs ws)=
      some (configuration (.some .clear) none [] bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_left]

theorem borrow_false (v : Option Bool) (as bs ws : List Bool) :
    TM2.step program (configuration (.some .borrow) v (false::as) bs ws)=
      some (configuration (.some .borrow) (some false) as (true::bs) ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,Bool.cond_false,update_stackData_left,update_stackData_right]

theorem borrow_true_nil (v : Option Bool) (bs ws : List Bool) :
    TM2.step program (configuration (.some .borrow) v [true] bs ws)=
      some (configuration (.some .restore) none [] bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,stackData_right,List.head?_cons,List.tail_cons,
    List.head?_nil,Option.isSome_some,Option.isSome_none,Option.getD_some,Bool.cond_true,Bool.cond_false,
    update_stackData_left]

theorem borrow_true_cons (v : Option Bool) (b : Bool) (as bs ws : List Bool) :
    TM2.step program (configuration (.some .borrow) v (true::b::as) bs ws)=
      some (configuration (.some .drain) (some b) (b::as) (false::bs) ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_stackData_left,update_stackData_right]

theorem drain_nil (v : Option Bool) (bs ws : List Bool) :
    TM2.step program (configuration (.some .drain) v [] bs ws)=
      some (configuration (.some .restore) none [] bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_left]

theorem drain_cons (v : Option Bool) (a : Bool) (as bs ws : List Bool) :
    TM2.step program (configuration (.some .drain) v (a::as) bs ws)=
      some (configuration (.some .drain) (some a) as (a::bs) ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_left,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_stackData_left,update_stackData_right]

theorem restore_nil (v : Option Bool) (as ws : List Bool) :
    TM2.step program (configuration (.some .restore) v as [] ws)=
      some (configuration none none as [] ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_right,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_right]

theorem restore_cons (v : Option Bool) (a : Bool) (as bs ws : List Bool) :
    TM2.step program (configuration (.some .restore) v as (a::bs) ws)=
      some (configuration (.some .restore) (some a) (a::as) bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_right,stackData_left,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_stackData_right,update_stackData_left]

theorem clear_nil (v : Option Bool) (as ws : List Bool) :
    TM2.step program (configuration (.some .clear) v as [] ws)=
      some (configuration none none as [] ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_right,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_right]

theorem clear_cons (v : Option Bool) (a : Bool) (as bs ws : List Bool) :
    TM2.step program (configuration (.some .clear) v as (a::bs) ws)=
      some (configuration (.some .clear) (some a) as bs ws) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true,update_stackData_right]

theorem halt (v : Option Bool) (as bs ws : List Bool) : TM2.step program (configuration none v as bs ws)=none := rfl

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

theorem running_control_card : Fintype.card (Label×Option Bool)=12 := by decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q <;> simp only [program,ListAssemblyMachine.statementDepth] <;> omega

end CircuitRecursion.BinaryCounterMachine
