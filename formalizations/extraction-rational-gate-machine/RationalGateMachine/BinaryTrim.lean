import RationalGateMachine.BinaryFifths

namespace RationalGateMachine.BinaryTrim

open Turing CircuitRecursion ListAssemblyMachine

/-- Proof-side high-order zero removal. The finite machine below implements
it on the reversed scratch stack without inspecting an unbounded number. -/
def stripZeros : List Bool → List Bool
  | [] => []
  | false::bs => stripZeros bs
  | true::bs => true::bs

theorem stripZeros_length (as : List Bool) : (stripZeros as).length≤as.length := by
  induction as with
  | nil => rfl
  | cons b bs ih => cases b <;> simp only [stripZeros,List.length_cons] <;> omega

theorem stripZeros_append (as bs : List Bool) :
    stripZeros (as++bs)=match stripZeros as with
      | [] => stripZeros bs
      | c::cs => c::(cs++bs) := by
  induction as with
  | nil => rfl
  | cons b as ih =>
      cases b with
      | false => exact ih
      | true => rfl

def canonicalBits (as : List Bool) : List Bool := (stripZeros as.reverse).reverse

theorem canonicalBits_cons (b : Bool) (bs : List Bool) :
    canonicalBits (b::bs)=match canonicalBits bs with
      | [] => if b then [true] else []
      | c::cs => b::c::cs := by
  unfold canonicalBits
  rw [List.reverse_cons,stripZeros_append]
  cases ht : stripZeros bs.reverse with
  | nil => cases b <;> rfl
  | cons c cs =>
      have hn : (c::cs).reverse≠[] := by simp
      cases hr : (c::cs).reverse with
      | nil => exact (hn hr).elim
      | cons d ds =>
          simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,
            List.nil_append,List.cons_append]
          simpa only [List.reverse_cons] using congrArg (List.cons b) hr

theorem canonicalBits_eq_trim (as : List Bool) : canonicalBits as=(binaryTrimProgram as).bits := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
      rw [canonicalBits_cons,ih]
      cases ht : (binaryTrimProgram bs).bits with
      | nil => cases b <;> simp only [binaryTrimProgram,ht,Bool.false_eq_true,ite_false,ite_true]
      | cons c cs => simp only [binaryTrimProgram,ht]

inductive Label where
  | drain | strip | restore
  deriving DecidableEq
instance : Fintype Label := ⟨{.drain,.strip,.restore},by intro q;cases q <;> simp⟩
instance : Inhabited Label := ⟨.drain⟩

abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def configuration (l : Option Label) (v : Option Bool)
    (bits denominator scratch : List Bool) : Configuration :=
  ⟨l,v,ListAssemblyMachine.stackData bits denominator scratch⟩

/-- Actual finite trim program. The entire right stack is preserved. It is
available for the denominator of the preceding fifths transducer. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .drain => .pop .left (fun _ b => b)
      (.branch Option.isSome
        (.push .work (fun b => b.getD false) (.goto (fun _ => .drain)))
        (.goto (fun _ => .strip)))
  | .strip => .peek .work (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.goto (fun _ => .restore))
          (.pop .work (fun _ b => b) (.goto (fun _ => .strip))))
        .halt)
  | .restore => .pop .work (fun _ b => b)
      (.branch Option.isSome
        (.push .left (fun b => b.getD false) (.goto (fun _ => .restore)))
        .halt)

def advance : Option Configuration → Option Configuration :=
  fun c => c.bind (TM2.step program)

theorem drain_nil (v : Option Bool) (den scratch : List Bool) :
    TM2.step program (configuration (some .drain) v [] den scratch)=
      some (configuration (some .strip) none [] den scratch) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_left,update_stackData_left]

theorem drain_cons (v : Option Bool) (b : Bool) (bs den scratch : List Bool) :
    TM2.step program (configuration (some .drain) v (b::bs) den scratch)=
      some (configuration (some .drain) (some b) bs den (b::scratch)) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_left,update_stackData_left,
    stackData_work,update_stackData_work]

theorem strip_nil (v : Option Bool) (den : List Bool) :
    TM2.step program (configuration (some .strip) v [] den [])=
      some (configuration none none [] den []) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_work]

theorem strip_false (v : Option Bool) (bs den : List Bool) :
    TM2.step program (configuration (some .strip) v [] den (false::bs))=
      some (configuration (some .strip) (some false) [] den bs) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_work,update_stackData_work]

theorem strip_true (v : Option Bool) (bs den : List Bool) :
    TM2.step program (configuration (some .strip) v [] den (true::bs))=
      some (configuration (some .restore) (some true) [] den (true::bs)) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_work]

theorem restore_nil (v : Option Bool) (as den : List Bool) :
    TM2.step program (configuration (some .restore) v as den [])=
      some (configuration none none as den []) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_work,update_stackData_work]

theorem restore_cons (v : Option Bool) (b : Bool) (as bs den : List Bool) :
    TM2.step program (configuration (some .restore) v as den (b::bs))=
      some (configuration (some .restore) (some b) (b::as) den bs) := by
  simp [configuration,program,TM2.step,TM2.stepAux,stackData_work,update_stackData_work,
    stackData_left,update_stackData_left]

theorem drain_iterate (v : Option Bool) (as den scratch : List Bool) :
    advance^[as.length+1] (some (configuration (some .drain) v as den scratch))=
      some (configuration (some .strip) none [] den (as.reverse++scratch)) := by
  induction as generalizing v scratch with
  | nil => exact drain_nil v den scratch
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      change advance^[bs.length+1] (TM2.step program
        (configuration (some .drain) v (b::bs) den scratch))=_
      rw [drain_cons,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem restore_iterate (v : Option Bool) (as bs den : List Bool) :
    advance^[bs.length+1] (some (configuration (some .restore) v as den bs))=
      some (configuration none none (bs.reverse++as) den []) := by
  induction bs generalizing v as with
  | nil => exact restore_nil v as den
  | cons b bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      change advance^[bs.length+1] (TM2.step program
        (configuration (some .restore) v as den (b::bs)))=_
      rw [restore_cons,ih]
      simp [List.reverse_cons,List.append_assoc]

def stripTime : List Bool → ℕ
  | [] => 1
  | false::bs => stripTime bs+1
  | true::bs => bs.length+3

theorem stripTime_bound (as : List Bool) : stripTime as≤as.length+2 := by
  induction as with
  | nil => decide
  | cons b bs ih => cases b <;> simp only [stripTime,List.length_cons] <;> omega

theorem strip_iterate (v : Option Bool) (as den : List Bool) :
    advance^[stripTime as] (some (configuration (some .strip) v [] den as))=
      some (configuration none none (stripZeros as).reverse den []) := by
  induction as generalizing v with
  | nil => exact strip_nil v den
  | cons b bs ih =>
      cases b with
      | false =>
          rw [stripTime,Function.iterate_succ_apply]
          change advance^[stripTime bs]
            (TM2.step program (configuration (some .strip) v [] den (false::bs)))=_
          rw [strip_false,ih];rfl
      | true =>
          rw [stripTime,show bs.length+3=((true::bs).length+1)+1 by simp,
            Function.iterate_succ_apply]
          change advance^[(true::bs).length+1]
            (TM2.step program (configuration (some .strip) v [] den (true::bs)))=_
          rw [strip_true,restore_iterate]
          simp [stripZeros]

def trimRun (as den : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .drain) none as den [])
      (some (configuration none none (binaryTrimProgram as).bits den [])) (2*as.length+3) := by
  refine ⟨⟨stripTime as.reverse+(as.length+1),?_⟩,?_⟩
  · change advance^[stripTime as.reverse+(as.length+1)]
      (some (configuration (some .drain) none as den []))=_
    rw [Function.iterate_add_apply,drain_iterate,List.append_nil,strip_iterate]
    rw [←canonicalBits_eq_trim];rfl
  · change stripTime as.reverse+(as.length+1)≤2*as.length+3
    have h:=stripTime_bound as.reverse
    simp only [List.length_reverse] at h
    omega

theorem trimRun_steps (as den : List Bool) :
    (trimRun as den).steps=stripTime as.reverse+(as.length+1) := rfl

theorem terminal_halts (as den : List Bool) : TM2.step program (configuration none none as den [])=none := rfl

theorem trim_mem_eval (as den : List Bool) :
    configuration none none (binaryTrimProgram as).bits den [] ∈ StateTransition.eval (TM2.step program)
      (configuration (some .drain) none as den []) :=
  evalsTo_terminal_mem_eval (trimRun as den).toEvalsTo (terminal_halts _ _)

theorem output_canonical (as den : List Bool) :
    BinaryWordCanonical ((configuration none none (binaryTrimProgram as).bits den []).stk .left) :=
  binaryTrimProgram_canonical as

theorem output_value (as den : List Bool) :
    binaryWordValue ((configuration none none (binaryTrimProgram as).bits den []).stk .left)=binaryWordValue as :=
  binaryTrimProgram_value as

theorem output_denominator (as den : List Bool) :
    (configuration none none (binaryTrimProgram as).bits den []).stk .right=den := rfl

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤5 := by
  cases q <;> simp only [program,ListAssemblyMachine.statementDepth] <;> omega

theorem finite_running_control_card : Fintype.card (Label × Option Bool)=9 := by decide

end RationalGateMachine.BinaryTrim
