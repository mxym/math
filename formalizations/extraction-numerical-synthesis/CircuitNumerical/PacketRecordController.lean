import CircuitNumerical.PacketRecordPrimitives

namespace CircuitRecursion.PacketRecordMachine

open Turing ListAssemblyMachine PacketFraming

inductive Label where
  | counter : BinaryCounterMachine.Label → Label
  | skip
  | copy : PacketFrameMachine.CopyLabel → Label
  | check
  | done
  deriving DecidableEq
instance : Fintype Label := ⟨{.counter .borrow,.counter .drain,.counter .restore,.counter .clear,
    .skip,.copy .scan,.copy .restore,.check,.done},by
  intro x;cases x with
  | counter q => cases q <;> simp
  | skip => simp
  | copy q => cases q <;> simp
  | check => simp
  | done => simp⟩
instance : Inhabited Label := ⟨.check⟩

/-- Whole variable-record reader. Subroutine syntax is compiled into these
finite labels; there are no host calls, Nat indices, runtime frame lengths,
or infinite packet-valued alphabet symbols in this program. -/
def program : Label → TM2.Stmt (fun _ : Stack => Symbol) Label (Option Symbol)
  | .counter q => TM2Subroutine.redirect Label.counter (fun _ => Label.skip) (PacketCounterLift.program q)
  | .skip => TM2Subroutine.redirect (fun _ : Unit => Label.skip) (fun _ => Label.check) (skipProgram ())
  | .copy q => TM2Subroutine.redirect Label.copy (fun _ => Label.done) (copyProgram q)
  | .check => .peek .work (fun _ x => x)
      (.branch Option.isSome
        (.peek .left (fun _ x => x)
          (.branch Option.isSome
            (.load (fun _ => none) (.goto (fun _ => .counter .borrow)))
            (.load (fun _ => none) (.goto (fun _ => .copy .scan)))))
        .halt)
  | .done => .halt

def advance : Option (Configuration Label) → Option (Configuration Label) := fun c => c.bind (TM2.step program)

theorem check_empty (v : Option Symbol) (index : List Symbol) :
    TM2.step program (configuration (some .check) v index [] [])=some (configuration none none index [] []) := by
  simp only [configuration,PacketStackPermutation.configuration,TM2.step,program,TM2.stepAux,stackData_work,
    List.head?_nil,Option.isSome_none,Bool.cond_false]

theorem check_zero (v : Option Symbol) (cache : List Symbol) (hc : cache≠[]) :
    TM2.step program (configuration (some .check) v [] [] cache)=
      some (configuration (some (.copy .scan)) none [] [] cache) := by
  cases cache with
  | nil => exact (hc rfl).elim
  | cons a as => simp only [configuration,PacketStackPermutation.configuration,TM2.step,program,TM2.stepAux,
      stackData_work,stackData_left,List.head?_cons,List.head?_nil,Option.isSome_some,Option.isSome_none,
      Bool.cond_false,Bool.cond_true]

theorem check_positive (v : Option Symbol) (bs : List Bool) (hb : bs≠[]) (cache : List Symbol) (hc : cache≠[]) :
    TM2.step program (configuration (some .check) v (bs.map Symbol.bit) [] cache)=
      some (configuration (some (.counter .borrow)) none (bs.map Symbol.bit) [] cache) := by
  cases cache with
  | nil => exact (hc rfl).elim
  | cons a as =>
    cases bs with
    | nil => exact (hb rfl).elim
    | cons b bs => simp only [configuration,PacketStackPermutation.configuration,TM2.step,program,TM2.stepAux,
        stackData_work,stackData_left,List.map_cons,List.head?_cons,Option.isSome_some,Bool.cond_true]

theorem done_step (v : Option Symbol) (output cache : List Symbol) :
    TM2.step program (configuration (some .done) v output [] cache)=some (configuration none v output [] cache) := rfl

def counterCall (i : BinaryIndex) (cache : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.counter .borrow)) none (i.bits.map Symbol.bit) [] cache)
      (some (configuration (some .skip) none (i.predecessor.bits.map Symbol.bit) [] cache)) (2*i.bits.length+2) :=
  TM2Subroutine.redirectedRun Label.counter (fun _ => Label.skip) PacketCounterLift.program program (fun _ => rfl)
    (PacketCounterLift.counterRun i.bits i.canonical cache)

def skipCall (p : WordIntegerPacket) (rest index : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .skip) none index [] (encodePacket p++rest))
      (some (configuration (some .check) (some .endPacket) index [] rest)) (encodePacket p).length :=
  TM2Subroutine.redirectedRun (fun _ : Unit => Label.skip) (fun _ => Label.check) skipProgram program (fun _ => rfl)
    (skipRecordRun p rest index [])

def copyCall (p : WordIntegerPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.copy .scan)) none [] [] (encodePacket p++rest))
      (some (configuration (some .done) none (encodePacket p) [] rest)) (2*(encodePacket p).length+1) := by
  let run:=TM2Subroutine.redirectedRun Label.copy (fun _ => Label.done) copyProgram program (fun _ => rfl)
    (copyRecordRun p rest [])
  have hx:=run.evals_in_steps
  have hs : run.steps=2*(encodePacket p).length+1 := rfl
  refine ⟨⟨2*(encodePacket p).length+1,?_⟩,le_refl _⟩
  rw [hs] at hx
  simpa only [TM2Subroutine.liftConfiguration,configuration,PacketStackPermutation.configuration,List.append_nil] using hx

theorem counter_iterate (i : BinaryIndex) (cache : List Symbol) :
    advance^[BinaryCounterMachine.borrowTime i.bits 0]
      (some (configuration (some (.counter .borrow)) none (i.bits.map Symbol.bit) [] cache))=
      some (configuration (some .skip) none (i.predecessor.bits.map Symbol.bit) [] cache) :=
  (counterCall i cache).evals_in_steps

theorem skip_iterate (p : WordIntegerPacket) (rest index : List Symbol) :
    advance^[(encodePacket p).length]
      (some (configuration (some .skip) none index [] (encodePacket p++rest)))=
      some (configuration (some .check) (some .endPacket) index [] rest) :=
  (skipCall p rest index).evals_in_steps

theorem copy_iterate (p : WordIntegerPacket) (rest : List Symbol) :
    advance^[2*(encodePacket p).length+1]
      (some (configuration (some (.copy .scan)) none [] [] (encodePacket p++rest)))=
      some (configuration (some .done) none (encodePacket p) [] rest) :=
  (copyCall p rest).evals_in_steps

theorem encodePacket_nonempty (p : WordIntegerPacket) : encodePacket p≠[] := by
  intro he
  have hl:=encodeRaw_length (rawPacket p)
  change (encodePacket p).length=_ at hl
  rw [he,List.length_nil] at hl
  omega

def terminal : List WordIntegerPacket → BinaryIndex → Configuration Label
  | [],i => configuration none none (i.bits.map Symbol.bit) [] []
  | p::ps,i => match i.bits with
      | [] => configuration none none (encodePacket p) [] (encodeCache ps)
      | _::_ => terminal ps i.predecessor

/-- This is an external exact transition index; the reader program does
not compute these Nat expressions or inspect encoded packet lengths. -/
def readTime : List WordIntegerPacket → BinaryIndex → ℕ
  | [],_ => 1
  | p::ps,i => match i.bits with
      | [] => 2*(encodePacket p).length+3
      | _::_ => BinaryCounterMachine.borrowTime i.bits 0+(encodePacket p).length+1+readTime ps i.predecessor

end CircuitRecursion.PacketRecordMachine
