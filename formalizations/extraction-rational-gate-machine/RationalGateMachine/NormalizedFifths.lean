import RationalGateMachine.BinaryTrim
import RationalGateMachine.LabelLift

namespace RationalGateMachine.NormalizedFifths

open Turing RationalGateProvider CircuitRecursion ListAssemblyMachine

abbrev Label := BinaryFifths.Label ⊕ BinaryTrim.Label
abbrev Variable := BinaryFifths.Variable
abbrev Configuration := TM2.Cfg (fun _ : Stack => Bool) Label Variable

def configuration (l : Option Label) (r : Remainder) (v : Option Bool)
    (left right work : List Bool) : Configuration :=
  ⟨l,(r,v),ListAssemblyMachine.stackData left right work⟩

/-- One literal finite program. The previous binary-input fifths machine's
halt is a goto into the physical trim machine, whose own halt remains halt. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Variable :=
  TM2Subroutine.splice BinaryFifths.program (fun _ => BinaryTrim.Label.drain)
    (fun l => LabelLift.compile Sum.inr (StateLift.compile (BinaryTrim.program l)))

def start (initial : Remainder) (i : BinaryIndex) : Configuration :=
  configuration (some (.inl (.inl (.inr .loop)))) initial none i.bits [] []

def terminal (initial : Remainder) (q : ℕ) : Configuration :=
  configuration none (RationalGateProvider.run initial q).remainder none
    (binaryTrimProgram (RationalGateProvider.run initial q).bits).bits (denominatorBits q) []

def fifthsCall (initial : Remainder) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program) (start initial i)
      (some (configuration (some (.inr .drain)) (RationalGateProvider.run initial i.value).remainder none
        (RationalGateProvider.run initial i.value).bits (denominatorBits i.value) []))
      ((2*i.bits.length+5)*i.value+3) :=
  TM2Subroutine.spliceRun BinaryFifths.program (fun _ => BinaryTrim.Label.drain)
    (fun l => LabelLift.compile Sum.inr (StateLift.compile (BinaryTrim.program l)))
    (BinaryFifths.binaryFifthsRun initial i)

def trimCall (initial : Remainder) (q : ℕ) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inr .drain)) (RationalGateProvider.run initial q).remainder none
        (RationalGateProvider.run initial q).bits (denominatorBits q) [])
      (some (terminal initial q)) (2*(RationalGateProvider.run initial q).bits.length+3) :=
  LabelLift.run Sum.inr (fun l => StateLift.compile (BinaryTrim.program l)) program (fun _ => rfl)
    (StateLift.run (RationalGateProvider.run initial q).remainder BinaryTrim.program
      (BinaryTrim.trimRun (RationalGateProvider.run initial q).bits (denominatorBits q)))

/-- Complete same-program run from encoded precision through canonical
numerator output. The clock and denominator phases and physical zero trimming
are all included in the actual official transition count. -/
def normalizedRun (initial : Remainder) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program) (start initial i)
      (some (terminal initial i.value)) ((2*i.bits.length+7)*i.value+6) := by
  let h:=StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (fifthsCall initial i) (trimCall initial i.value)
  refine ⟨h.toEvalsTo,?_⟩
  have ht:=h.steps_le_m
  change h.steps≤(2*i.bits.length+7)*i.value+6
  have hl:=run_bits_length initial i.value
  nlinarith

theorem normalizedRun_steps (initial : Remainder) (i : BinaryIndex) :
    (normalizedRun initial i).steps=
      BinaryTrim.stripTime (RationalGateProvider.run initial i.value).bits.reverse+
        ((RationalGateProvider.run initial i.value).bits.length+1)+
        (BinaryClock.clockTime i.value i+i.value+2) := rfl

theorem normalizedRun_steps_logarithmic (initial : Remainder) (i : BinaryIndex) :
    (normalizedRun initial i).steps≤(2*Nat.clog 2 (i.value+1)+9)*i.value+6 := by
  have hs:=(normalizedRun initial i).steps_le_m
  have hw:=BinaryClock.input_width_logarithmic i
  have hm:=Nat.mul_le_mul_right i.value (show 2*i.bits.length+7≤2*Nat.clog 2 (i.value+1)+9 by omega)
  exact hs.trans (Nat.add_le_add_right hm 6)

theorem terminal_halts (initial : Remainder) (q : ℕ) : TM2.step program (terminal initial q)=none := rfl

theorem normalized_mem_eval (initial : Remainder) (i : BinaryIndex) :
    terminal initial i.value ∈ StateTransition.eval (TM2.step program) (start initial i) :=
  evalsTo_terminal_mem_eval (normalizedRun initial i).toEvalsTo (terminal_halts _ _)

theorem terminal_numerator_canonical (initial : Remainder) (q : ℕ) :
    BinaryWordCanonical ((terminal initial q).stk .left) := binaryTrimProgram_canonical _

theorem terminal_numerator_value (initial : Remainder) (q : ℕ) :
    binaryWordValue ((terminal initial q).stk .left)=binaryWordValue (RationalGateProvider.run initial q).bits :=
  binaryTrimProgram_value _

theorem terminal_denominator (initial : Remainder) (q : ℕ) :
    (terminal initial q).stk .right=denominatorBits q := rfl

theorem terminal_scratch_empty (initial : Remainder) (q : ℕ) : (terminal initial q).stk .work=[] := rfl

theorem wordValue_eq_providerValue (bs : List Bool) : binaryWordValue bs=bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [binaryWordValue,binaryBitValue,bitValue,ih]

theorem terminal_dyadic_error (initial : Remainder) (q : ℕ) :
    0≤(initial.value:ℚ)/5-(bitValue ((terminal initial q).stk .left):ℚ)/2^q ∧
      (initial.value:ℚ)/5-(bitValue ((terminal initial q).stk .left):ℚ)/2^q<1/(2:ℚ)^q := by
  have hv:=terminal_numerator_value initial q
  rw [wordValue_eq_providerValue,wordValue_eq_providerValue] at hv
  rw [hv]
  exact run_dyadic_error initial q

theorem program_supports : TM2.Supports program Finset.univ :=
  TM2Subroutine.splice_supports _ _ _

theorem finite_running_control_card : Fintype.card (Label × Variable)=165 := by
  rw [Fintype.card_prod,Fintype.card_sum,BinaryFifths.label_card]
  decide

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl q =>
      rw [program,TM2Subroutine.splice_local_statementDepth]
      exact BinaryFifths.statement_depth q
  | inr q =>
      rw [program,TM2Subroutine.splice_outer,LabelLift.statement_depth,StateLift.statement_depth]
      exact (BinaryTrim.statement_depth q).trans (by decide)

end RationalGateMachine.NormalizedFifths
