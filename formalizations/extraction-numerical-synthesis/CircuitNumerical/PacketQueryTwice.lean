import CircuitNumerical.PacketQuerySemantics

namespace CircuitRecursion.PacketQueryTwiceMachine

open Turing PacketFraming

abbrev Stack := PacketQueryMachine.Stack
abbrev Label := (Bool×PacketQueryMachine.Label) ⊕ Unit
abbrev Configuration := TM2.Cfg (fun _ : Stack => Symbol) Label (Option Symbol)

def embed (second : Bool) (q : PacketQueryMachine.Label) : Label := .inl (second,q)

def ret (second : Bool) (_ : Option Symbol) : Label :=
  if second then .inr () else .inl (true,.inl .clearIndex)

/-- A concrete finite caller performs two successive reads from one physical
query stream. The first return is a literal goto into the second clear loop;
its old output and cache suffix are really popped, with no host restart. -/
def program : Label → TM2.Stmt (fun _ : Stack => Symbol) Label (Option Symbol)
  | .inl (b,q) => TM2Subroutine.redirect (embed b) (ret b) (PacketQueryMachine.program q)
  | .inr _ => .halt

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

def firstReturn (ps : List WordIntegerPacket) (first second : BinaryIndex) (rest : List Symbol) : Configuration :=
  TM2Subroutine.liftConfiguration (embed false) (ret false)
    (PacketQueryMachine.terminal ps first (PacketQueryMachine.queryCode second.bits++rest))

def terminal (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) : Configuration :=
  ⟨none,(PacketQueryMachine.terminal ps last rest).var,(PacketQueryMachine.terminal ps last rest).stk⟩

def firstCall (ps : List WordIntegerPacket) (first second : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2Subroutine.liftConfiguration (embed false) (ret false)
        (PacketQueryMachine.configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps)
          (PacketQueryMachine.queryCode first.bits++(PacketQueryMachine.queryCode second.bits++rest))))
      (some (firstReturn ps first second rest)) (oldIndex.length+oldScratch.length+oldCache.length+
        2*first.bits.length+(2*first.bits.length+3)*ps.length+4*(encodeCache ps).length+10) :=
  TM2Subroutine.redirectedRun (embed false) (ret false) PacketQueryMachine.program program (fun _ => rfl)
    (PacketQueryMachine.nextQueryRun ps first v oldIndex oldScratch oldCache (PacketQueryMachine.queryCode second.bits++rest))

theorem firstReturn_reentry (ps : List WordIntegerPacket) (first second : BinaryIndex) (rest : List Symbol) :
    firstReturn ps first second rest=
      TM2Subroutine.liftConfiguration (embed true) (ret true)
        (PacketQueryMachine.reentry ps first (PacketQueryMachine.queryCode second.bits++rest)) := by
  simp only [firstReturn,TM2Subroutine.liftConfiguration,PacketQueryMachine.terminal_label]
  change TM2.Cfg.mk (some (embed true (.inl .clearIndex)))
      (PacketQueryMachine.terminal ps first (PacketQueryMachine.queryCode second.bits++rest)).var
      (PacketQueryMachine.terminal ps first (PacketQueryMachine.queryCode second.bits++rest)).stk=
    TM2.Cfg.mk (some (embed true (.inl .clearIndex)))
      (PacketQueryMachine.terminal ps first (PacketQueryMachine.queryCode second.bits++rest)).var
      (PacketQueryMachine.reentry ps first (PacketQueryMachine.queryCode second.bits++rest)).stk
  congr 1
  exact (PacketQueryMachine.reentry_stacks ps first _).symm

def secondCall (ps : List WordIntegerPacket) (first second : BinaryIndex) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2Subroutine.liftConfiguration (embed true) (ret true)
        (PacketQueryMachine.reentry ps first (PacketQueryMachine.queryCode second.bits++rest)))
      (some (TM2Subroutine.liftConfiguration (embed true) (ret true) (PacketQueryMachine.terminal ps second rest)))
      (first.bits.length+2*second.bits.length+(2*second.bits.length+3)*ps.length+5*(encodeCache ps).length+10) :=
  TM2Subroutine.redirectedRun (embed true) (ret true) PacketQueryMachine.program program (fun _ => rfl)
    (PacketQueryMachine.reuseRun ps first second rest)

theorem finish_step (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) :
    TM2.step program
      (TM2Subroutine.liftConfiguration (embed true) (ret true) (PacketQueryMachine.terminal ps last rest))=
      some (terminal ps last rest) := by
  simp only [TM2Subroutine.liftConfiguration,PacketQueryMachine.terminal_label,ret,ite_true,
    TM2.step,program,TM2.stepAux,terminal]

/-- Two complete real calls and one final halt transition. All second-query
cleanup is evaluated from the actual first terminal contents and bounded
internally, rather than replaced by a caller-supplied cleanup certificate. -/
def twoQueryRun (ps : List WordIntegerPacket) (first second : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2Subroutine.liftConfiguration (embed false) (ret false)
        (PacketQueryMachine.configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps)
          (PacketQueryMachine.queryCode first.bits++(PacketQueryMachine.queryCode second.bits++rest))))
      (some (terminal ps second rest)) (oldIndex.length+oldScratch.length+oldCache.length+
        3*first.bits.length+2*second.bits.length+(2*first.bits.length+2*second.bits.length+6)*ps.length+
        9*(encodeCache ps).length+21) :=
  let h₁:=firstCall ps first second v oldIndex oldScratch oldCache rest
  let h₂:=secondCall ps first second rest
  ⟨⟨h₂.steps+h₁.steps+1,by
    change advance^[h₂.steps+h₁.steps+1] _=_
    rw [show h₂.steps+h₁.steps+1=1+(h₂.steps+h₁.steps) by omega,
      Function.iterate_add_apply,Function.iterate_add_apply]
    have hx₁ : advance^[h₁.steps] _=some (firstReturn ps first second rest) := h₁.evals_in_steps
    rw [hx₁,firstReturn_reentry]
    have hx₂ : advance^[h₂.steps] _=some (TM2Subroutine.liftConfiguration (embed true) (ret true)
      (PacketQueryMachine.terminal ps second rest)) := h₂.evals_in_steps
    rw [hx₂]
    exact finish_step ps second rest⟩,by
    change h₂.steps+h₁.steps+1≤_
    have ht₁:=h₁.steps_le_m
    have ht₂:=h₂.steps_le_m
    nlinarith⟩

theorem terminal_halts (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) :
    TM2.step program (terminal ps last rest)=none := rfl

theorem twoQuery_mem_eval (ps : List WordIntegerPacket) (first second : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) : terminal ps second rest∈StateTransition.eval (TM2.step program)
      (TM2Subroutine.liftConfiguration (embed false) (ret false)
        (PacketQueryMachine.configuration (some (.inl .clearIndex)) v oldIndex oldScratch oldCache (encodeCache ps)
          (PacketQueryMachine.queryCode first.bits++(PacketQueryMachine.queryCode second.bits++rest)))) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval
    (twoQueryRun ps first second v oldIndex oldScratch oldCache rest).toEvalsTo (terminal_halts ps second rest)

theorem terminal_master (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) :
    (terminal ps last rest).stk (.inl (.inr ()))=encodeCache ps := PacketQueryMachine.terminal_master ps last rest

theorem terminal_queries (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) :
    (terminal ps last rest).stk (.inr ())=rest := rfl

theorem firstReturn_encoded_getElem (ps : List WordIntegerPacket) (first second : BinaryIndex) (rest : List Symbol)
    (p : WordIntegerPacket) (hp : ps[first.value]?=some p) :
    (firstReturn ps first second rest).stk (.inl (.inl .left))=encodePacket p :=
  PacketQueryMachine.terminal_encoded_getElem ps first (PacketQueryMachine.queryCode second.bits++rest) p hp

theorem terminal_encoded_getElem (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol)
    (p : WordIntegerPacket) (hp : ps[last.value]?=some p) :
    (terminal ps last rest).stk (.inl (.inl .left))=encodePacket p :=
  PacketQueryMachine.terminal_encoded_getElem ps last rest p hp

theorem terminal_cache_tail (ps : List WordIntegerPacket) (last : BinaryIndex) (rest : List Symbol) :
    (terminal ps last rest).stk (.inl (.inl .work))=encodeCache (ps.drop (last.value+1)) :=
  PacketQueryMachine.terminal_cache_tail ps last rest

theorem twoQueryRun_steps_height (ps : List WordIntegerPacket) (first second : BinaryIndex) (v : Option Symbol)
    (oldIndex oldScratch oldCache rest : List Symbol) (B : ℕ) (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (twoQueryRun ps first second v oldIndex oldScratch oldCache rest).steps≤
      oldIndex.length+oldScratch.length+oldCache.length+3*first.bits.length+2*second.bits.length+
        (2*first.bits.length+2*second.bits.length+45*B+132)*ps.length+21 := by
  have hs:=(twoQueryRun ps first second v oldIndex oldScratch oldCache rest).steps_le_m
  have hc:=encodeCache_length_height ps B h
  nlinarith

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Option Symbol)=165 := by
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_unit]
  have hs : Fintype.card (Option Symbol)=5 := by decide
  have hq : Fintype.card PacketQueryMachine.Label=16 := by
    have h:=PacketQueryMachine.running_control_card
    rw [Fintype.card_prod,hs] at h
    omega
  rw [hs,hq]

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤7 := by
  cases q with
  | inl bq =>
    rcases bq with ⟨b,q⟩
    rw [program,TM2Subroutine.redirect_statementDepth]
    exact PacketQueryMachine.statement_depth q
  | inr u => simp only [program,ListAssemblyMachine.statementDepth];omega

end CircuitRecursion.PacketQueryTwiceMachine
