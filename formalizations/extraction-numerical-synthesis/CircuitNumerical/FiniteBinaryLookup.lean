import CircuitNumerical.TM2SubroutineSplice

namespace CircuitRecursion.BinaryLookupMachine

open Turing ListAssemblyMachine

inductive OuterLabel where
  | check | advance
  deriving DecidableEq
instance : Fintype OuterLabel := ⟨{.check,.advance},by intro x;cases x <;> simp⟩
instance : Inhabited OuterLabel := ⟨.check⟩

abbrev Label := BinaryCounterMachine.Label⊕OuterLabel
abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def configuration (l : Option Label) (v : Option Bool) (index scratch cache : List Bool) : Configuration :=
  ⟨l,v,stackData index scratch cache⟩

/-- The caller checks actual stack constructors, calls the finite binary
counter, then drops one cache cell. No Nat decode/index/fuel occurs. -/
def outer : OuterLabel → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .check => .peek .work (fun _ x => x)
      (.branch Option.isSome
        (.peek .left (fun _ x => x)
          (.branch Option.isSome
            (.load (fun _ => none) (.goto (fun _ => .inl .borrow)))
            .halt))
        .halt)
  | .advance => .pop .work (fun _ _ => none) (.goto (fun _ => .inr .check))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  TM2Subroutine.splice BinaryCounterMachine.program (fun _ => .advance) outer

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

theorem check_empty (v : Option Bool) (i s : List Bool) :
    TM2.step program (configuration (some (.inr .check)) v i s [])=
      some (configuration none none i s []) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,stackData_work,
    List.head?_nil,Option.isSome_none,Bool.cond_false]

theorem check_zero (v : Option Bool) (b : Bool) (bs s : List Bool) :
    TM2.step program (configuration (some (.inr .check)) v [] s (b::bs))=
      some (configuration none none [] s (b::bs)) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,stackData_work,stackData_left,
    List.head?_nil,List.head?_cons,Option.isSome_none,Option.isSome_some,Bool.cond_false,Bool.cond_true]

theorem check_nonzero (v : Option Bool) (a b : Bool) (as bs s : List Bool) :
    TM2.step program (configuration (some (.inr .check)) v (a::as) s (b::bs))=
      some (configuration (some (.inl .borrow)) none (a::as) s (b::bs)) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,stackData_work,stackData_left,
    List.head?_cons,Option.isSome_some,Bool.cond_true]

theorem advance_cons (v : Option Bool) (a : Bool) (i s cache : List Bool) :
    TM2.step program (configuration (some (.inr .advance)) v i s (a::cache))=
      some (configuration (some (.inr .check)) none i s cache) := by
  simp only [program,TM2Subroutine.splice,outer,configuration,TM2.step,TM2.stepAux,stackData_work,
    List.tail_cons,update_stackData_work]

/-- Actual inlined counter execution, returning to the caller's advance
label in the very same machine. No independent cost premise is required. -/
def counterInvocation (i : BinaryIndex) (cache : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .borrow)) none i.bits [] cache)
      (some (configuration (some (.inr .advance)) none i.predecessor.bits [] cache)) (2*i.bits.length+2) :=
  TM2Subroutine.counterCall (fun _ : Option Bool => OuterLabel.advance) outer i.bits i.canonical cache

theorem counter_iterate (i : BinaryIndex) (cache : List Bool) :
    advance^[BinaryCounterMachine.borrowTime i.bits 0]
      (some (configuration (some (.inl .borrow)) none i.bits [] cache))=
      some (configuration (some (.inr .advance)) none i.predecessor.bits [] cache) :=
  (counterInvocation i cache).evals_in_steps

def terminal : List Bool → BinaryIndex → Configuration
  | [],i => configuration none none i.bits [] []
  | a::as,i => match i.bits with
      | [] => configuration none none [] [] (a::as)
      | _::_ => terminal as i.predecessor

/-- External exact time function, not a Nat register in the machine. -/
def lookupTime : List Bool → BinaryIndex → ℕ
  | [],_ => 1
  | _::as,i => match i.bits with
      | [] => 1
      | _::_ => BinaryCounterMachine.borrowTime i.bits 0+2+lookupTime as i.predecessor

theorem lookup_iterate (cache : List Bool) (i : BinaryIndex) :
    advance^[lookupTime cache i] (some (configuration (some (.inr .check)) none i.bits [] cache))=
      some (terminal cache i) := by
  induction cache generalizing i with
  | nil => exact check_empty none i.bits []
  | cons b bs ih =>
    cases hb : i.bits with
    | nil =>
      simp only [lookupTime,terminal,hb]
      change TM2.step program (configuration (some (.inr .check)) none [] [] (b::bs))=_
      exact check_zero none b bs []
    | cons a as =>
      have hc:=counter_iterate i (b::bs)
      simp only [hb] at hc
      simp only [lookupTime,terminal,hb]
      rw [show BinaryCounterMachine.borrowTime (a::as) 0+2+lookupTime bs i.predecessor=
        (lookupTime bs i.predecessor+1+BinaryCounterMachine.borrowTime (a::as) 0)+1 by omega,
        Function.iterate_succ_apply]
      change advance^[lookupTime bs i.predecessor+1+BinaryCounterMachine.borrowTime (a::as) 0]
        (TM2.step program (configuration (some (.inr .check)) none (a::as) [] (b::bs)))=_
      rw [check_nonzero,Function.iterate_add_apply,hc,Function.iterate_succ_apply]
      change advance^[lookupTime bs i.predecessor]
        (TM2.step program (configuration (some (.inr .advance)) none i.predecessor.bits [] (b::bs)))=_
      rw [advance_cons,ih]

end CircuitRecursion.BinaryLookupMachine
