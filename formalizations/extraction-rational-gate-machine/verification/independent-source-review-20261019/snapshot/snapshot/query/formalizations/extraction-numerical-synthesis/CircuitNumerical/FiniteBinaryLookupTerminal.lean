import CircuitNumerical.FiniteBinaryLookup

namespace CircuitRecursion.BinaryLookupMachine

theorem lookupTime_trace (cache : List Bool) (i : BinaryIndex) :
    lookupTime cache i=(binaryIndexedLookup cache i).trace.counterTransitions+
      2*(binaryIndexedLookup cache i).trace.counterCalls+1 := by
  induction cache generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases hb : i.bits with
    | nil => simp only [lookupTime,binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterTransitions,
        BinaryIndexedLookupTrace.counterCalls]
    | cons a as =>
      have hi:=ih i.predecessor
      simp only [lookupTime,binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterTransitions,
        BinaryIndexedLookupTrace.counterCalls,BinaryCounterMachine.counterRun_steps]
      omega

theorem lookupTime_bound (cache : List Bool) (i : BinaryIndex) :
    lookupTime cache i≤(2*i.bits.length+4)*cache.length+1 := by
  rw [lookupTime_trace]
  have ht:=binaryIndexedLookup_counterTransitions cache i
  have hc:=binaryIndexedLookup_counterCalls cache i
  nlinarith

/-- A full execution of the actual six-label finite Boolean lookup machine.
The binary counter is compiled inline; no host call or Nat arithmetic is
charged as a unit operation. The clock here is only a proved time index. -/
def lookupRun (cache : List Bool) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (Turing.TM2.step program)
      (configuration (some (.inr .check)) none i.bits [] cache)
      (some (terminal cache i)) ((2*i.bits.length+4)*cache.length+1) :=
  ⟨⟨lookupTime cache i,lookup_iterate cache i⟩,lookupTime_bound cache i⟩

theorem lookupRun_steps (cache : List Bool) (i : BinaryIndex) : (lookupRun cache i).steps=lookupTime cache i := rfl

theorem lookupRun_steps_trace (cache : List Bool) (i : BinaryIndex) :
    (lookupRun cache i).steps=(binaryIndexedLookup cache i).trace.counterTransitions+
      2*(binaryIndexedLookup cache i).trace.counterCalls+1 := lookupTime_trace cache i

theorem terminal_label (cache : List Bool) (i : BinaryIndex) : (terminal cache i).l=none := by
  induction cache generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases hb : i.bits with
    | nil => simp only [terminal,hb,configuration]
    | cons a as => simpa only [terminal,hb] using ih i.predecessor

theorem terminal_halts (cache : List Bool) (i : BinaryIndex) : Turing.TM2.step program (terminal cache i)=none := by
  have hl:=terminal_label cache i
  cases ht : terminal cache i with
  | mk l v S =>
    rw [ht] at hl
    change l=none at hl
    subst l
    rfl

theorem lookup_mem_eval (cache : List Bool) (i : BinaryIndex) :
    terminal cache i∈StateTransition.eval (Turing.TM2.step program)
      (configuration (some (.inr .check)) none i.bits [] cache) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (lookupRun cache i).toEvalsTo (terminal_halts cache i)

theorem terminal_source_value (cache : List Bool) (i : BinaryIndex) :
    ((terminal cache i).stk .work).head?=(binaryIndexedLookup cache i).value := by
  induction cache generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases hb : i.bits with
    | nil => simp only [terminal,binaryIndexedLookup,hb,configuration,ListAssemblyMachine.stackData_work,List.head?_cons]
    | cons a as => simpa only [terminal,binaryIndexedLookup,hb] using ih i.predecessor

theorem terminal_getElem (cache : List Bool) (i : BinaryIndex) :
    ((terminal cache i).stk .work).head?=cache[i.value]? := by
  rw [terminal_source_value,binaryIndexedLookup_getElem]

theorem lookupRun_steps_height (cache : List Bool) (i : BinaryIndex) (B : ℕ)
    (hv : i.value≤2^B) : (lookupRun cache i).steps≤(2*B+6)*cache.length+1 := by
  have hw:=binaryWordCanonical_width i.bits i.canonical B hv
  have hs:=(lookupRun cache i).steps_le_m
  have hm:=Nat.mul_le_mul_right cache.length (show 2*i.bits.length+4≤2*B+6 by omega)
  exact hs.trans (Nat.add_le_add_right hm 1)

theorem program_supports : Turing.TM2.Supports program Finset.univ :=
  TM2Subroutine.splice_supports _ _ _

theorem running_control_card : Fintype.card (Label×Option Bool)=18 := by decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl l =>
    rw [program,TM2Subroutine.splice_local_statementDepth]
    exact BinaryCounterMachine.statement_depth l
  | inr l =>
    cases l <;> simp only [program,TM2Subroutine.splice,outer,ListAssemblyMachine.statementDepth] <;> omega

end CircuitRecursion.BinaryLookupMachine
