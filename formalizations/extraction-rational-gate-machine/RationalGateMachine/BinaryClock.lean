import RationalGateMachine.Fifths
import CircuitNumerical.TM2SubroutineSplice

namespace RationalGateMachine.BinaryClock

open Turing CircuitRecursion
open ListAssemblyMachine

inductive OuterLabel where
  | loop | emit
  deriving DecidableEq
instance : Fintype OuterLabel := ⟨{.loop,.emit}, by intro q; cases q <;> simp⟩
instance : Inhabited OuterLabel := ⟨.loop⟩

abbrev Label := BinaryCounterMachine.Label ⊕ OuterLabel
abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def configuration (l : Option Label) (v : Option Bool)
    (counter scratch clock : List Bool) : Configuration :=
  ⟨l, v, ListAssemblyMachine.stackData counter scratch clock⟩

/-- Finite binary-to-unary loop. No precision value, Nat fuel or counter
annotation is read by this official machine program. -/
def outer : OuterLabel → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .loop => .peek .left (fun _ b => b)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => .inl .borrow)))
        .halt)
  | .emit => .push .work (fun _ => false) (.goto (fun _ => .inr .loop))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  TM2Subroutine.splice BinaryCounterMachine.program (fun _ => .emit) outer

def liftedStep : Option Configuration → Option Configuration :=
  fun c => c.bind (TM2.step program)

theorem step_zero (v : Option Bool) (scratch clock : List Bool) :
    TM2.step program (configuration (some (.inr .loop)) v [] scratch clock) =
      some (configuration none none [] scratch clock) := by
  simp only [program, TM2Subroutine.splice, outer, configuration, TM2.step, TM2.stepAux,
    stackData_left, List.head?_nil, Option.isSome_none, Bool.cond_false]

theorem step_positive (v : Option Bool) (b : Bool) (bs scratch clock : List Bool) :
    TM2.step program (configuration (some (.inr .loop)) v (b::bs) scratch clock) =
      some (configuration (some (.inl .borrow)) none (b::bs) scratch clock) := by
  simp only [program, TM2Subroutine.splice, outer, configuration, TM2.step, TM2.stepAux,
    stackData_left, List.head?_cons, Option.isSome_some, Bool.cond_true]

theorem step_emit (v : Option Bool) (counter scratch clock : List Bool) :
    TM2.step program (configuration (some (.inr .emit)) v counter scratch clock) =
      some (configuration (some (.inr .loop)) v counter scratch (false::clock)) := by
  simp only [program, TM2Subroutine.splice, outer, configuration, TM2.step, TM2.stepAux,
    stackData_work, update_stackData_work]

def counterInvocation (i : BinaryIndex) (clock : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .borrow)) none i.bits [] clock)
      (some (configuration (some (.inr .emit)) none i.predecessor.bits [] clock))
      (2*i.bits.length+2) :=
  TM2Subroutine.counterCall (fun _ : Option Bool => OuterLabel.emit) outer i.bits i.canonical clock

theorem counter_iterate (i : BinaryIndex) (clock : List Bool) :
    liftedStep^[BinaryCounterMachine.borrowTime i.bits 0]
      (some (configuration (some (.inl .borrow)) none i.bits [] clock)) =
      some (configuration (some (.inr .emit)) none i.predecessor.bits [] clock) :=
  (counterInvocation i clock).evals_in_steps

/-- External proof-side exact time. q is never a register or fuel argument
to program. The final run sets it to the semantic input value internally. -/
def clockTime : ℕ → BinaryIndex → ℕ
  | 0, _ => 1
  | q+1, i => BinaryCounterMachine.borrowTime i.bits 0 + 2 + clockTime q i.predecessor

theorem clock_time_bound (q : ℕ) (i : BinaryIndex) :
    clockTime q i ≤ (2*i.bits.length+4)*q+1 := by
  induction q generalizing i with
  | zero => simp [clockTime]
  | succ q ih =>
      have hcounter := BinaryCounterMachine.borrowTime_bound i.bits 0
      have htail := (ih i.predecessor).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_right q (show 2*i.predecessor.bits.length+4 ≤ 2*i.bits.length+4 by
          have hw := i.predecessor_width
          omega)) 1)
      calc
        clockTime (q+1) i = BinaryCounterMachine.borrowTime i.bits 0 + 2 + clockTime q i.predecessor := rfl
        _ ≤ (2*i.bits.length+2) + 2 + ((2*i.bits.length+4)*q+1) :=
          Nat.add_le_add (Nat.add_le_add_right (by simpa using hcounter) 2) htail
        _ = (2*i.bits.length+4)*(q+1)+1 := by ring

theorem clock_iterate (q : ℕ) (i : BinaryIndex) (hi : i.value = q) (clock : List Bool) :
    liftedStep^[clockTime q i]
      (some (configuration (some (.inr .loop)) none i.bits [] clock)) =
      some (configuration none none [] [] (List.replicate q false ++ clock)) := by
  induction q generalizing i clock with
  | zero =>
      have hz : i.bits = [] := (binaryWordCanonical_zero_iff i.bits i.canonical).mp hi
      simp only [clockTime, hz, List.replicate_zero, List.nil_append]
      exact step_zero none [] clock
  | succ q ih =>
      have hne : i.bits ≠ [] := by
        intro hz
        have hv : i.value = 0 := by simp [BinaryIndex.value, hz, binaryWordValue]
        omega
      have hp := i.predecessor_progress hne
      have hpred : i.predecessor.value = q := by omega
      cases hb : i.bits with
      | nil => exact False.elim (hne hb)
      | cons b bs =>
          have hc := counter_iterate i clock
          simp only [hb] at hc
          simp only [clockTime, hb]
          rw [show BinaryCounterMachine.borrowTime (b::bs) 0+2+clockTime q i.predecessor =
            (clockTime q i.predecessor+1+BinaryCounterMachine.borrowTime (b::bs) 0)+1 by omega,
            Function.iterate_succ_apply]
          change liftedStep^[clockTime q i.predecessor+1+BinaryCounterMachine.borrowTime (b::bs) 0]
            (TM2.step program (configuration (some (.inr .loop)) none (b::bs) [] clock)) = _
          rw [step_positive, Function.iterate_add_apply, hc, Function.iterate_succ_apply]
          change liftedStep^[clockTime q i.predecessor]
            (TM2.step program (configuration (some (.inr .emit)) none i.predecessor.bits [] clock)) = _
          rw [step_emit, ih i.predecessor hpred (false::clock)]
          congr 2
          rw [List.replicate_add]
          simp [List.append_assoc]

def clockRun (i : BinaryIndex) (clock : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inr .loop)) none i.bits [] clock)
      (some (configuration none none [] [] (List.replicate i.value false ++ clock)))
      ((2*i.bits.length+4)*i.value+1) :=
  ⟨⟨clockTime i.value i, clock_iterate i.value i rfl clock⟩, clock_time_bound i.value i⟩

theorem clockRun_steps (i : BinaryIndex) (clock : List Bool) :
    (clockRun i clock).steps = clockTime i.value i := rfl

theorem clockRun_steps_width (i : BinaryIndex) (clock : List Bool) :
    (clockRun i clock).steps ≤ (2*i.bits.length+4)*i.value+1 :=
  clock_time_bound i.value i

theorem input_width_logarithmic (i : BinaryIndex) :
    i.bits.length ≤ Nat.clog 2 (i.value+1)+1 := by
  apply binaryWordCanonical_width i.bits i.canonical
  exact (Nat.le_succ i.value).trans (Nat.le_pow_clog (by decide) (i.value+1))

/-- Actual transitions of the same run, after internally bounding canonical
input width. The decoded value occurs only in this specification. -/
theorem clockRun_steps_logarithmic (i : BinaryIndex) (clock : List Bool) :
    (clockRun i clock).steps ≤ (2*Nat.clog 2 (i.value+1)+6)*i.value+1 := by
  apply (clockRun_steps_width i clock).trans
  have hw := input_width_logarithmic i
  exact Nat.add_le_add_right (Nat.mul_le_mul_right i.value (by omega)) 1

theorem terminal_halts (clock : List Bool) :
    TM2.step program (configuration none none [] [] clock) = none := rfl

theorem clock_mem_eval (i : BinaryIndex) (clock : List Bool) :
    configuration none none [] [] (List.replicate i.value false ++ clock) ∈
      StateTransition.eval (TM2.step program)
        (configuration (some (.inr .loop)) none i.bits [] clock) :=
  evalsTo_terminal_mem_eval (clockRun i clock).toEvalsTo (terminal_halts _)

theorem program_supports : TM2.Supports program Finset.univ :=
  TM2Subroutine.splice_supports _ _ _

theorem finite_running_control_card : Fintype.card (Label × Option Bool) = 18 := by decide

theorem outer_statement_depth (q : OuterLabel) : statementDepth (outer q) ≤ 4 := by
  cases q <;> simp [outer, statementDepth]

end RationalGateMachine.BinaryClock
