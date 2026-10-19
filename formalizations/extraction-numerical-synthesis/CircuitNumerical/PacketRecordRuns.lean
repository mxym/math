import CircuitNumerical.PacketRecordController

namespace CircuitRecursion.PacketRecordMachine

open Turing ListAssemblyMachine PacketFraming

set_option maxHeartbeats 1500000

theorem frame_append_nonempty (p : WordIntegerPacket) (rest : List Symbol) : encodePacket p++rest≠[] := by
  cases hp : encodePacket p with
  | nil => exact (encodePacket_nonempty p hp).elim
  | cons a as => exact List.cons_ne_nil _ _

theorem read_iterate (ps : List WordIntegerPacket) (i : BinaryIndex) (v : Option Symbol) :
    advance^[readTime ps i]
      (some (configuration (some .check) v (i.bits.map Symbol.bit) [] (encodeCache ps)))=
      some (terminal ps i) := by
  induction ps generalizing i v with
  | nil => exact check_empty v (i.bits.map Symbol.bit)
  | cons p ps ih =>
    have hc:=frame_append_nonempty p (encodeCache ps)
    cases hb : i.bits with
    | nil =>
      simp only [readTime,terminal,hb,List.map_nil,encodeCache]
      rw [show 2*(encodePacket p).length+3=(1+(2*(encodePacket p).length+1))+1 by omega,
        Function.iterate_succ_apply]
      change advance^[1+(2*(encodePacket p).length+1)]
        (TM2.step program (configuration (some .check) v [] [] (encodePacket p++encodeCache ps)))=_
      rw [check_zero v _ hc,Function.iterate_add_apply,copy_iterate]
      exact done_step none (encodePacket p) (encodeCache ps)
    | cons b bs =>
      have hcounter:=counter_iterate i (encodePacket p++encodeCache ps)
      simp only [hb] at hcounter
      simp only [readTime,terminal,hb,encodeCache]
      rw [show BinaryCounterMachine.borrowTime (b::bs) 0+(encodePacket p).length+1+readTime ps i.predecessor=
        (readTime ps i.predecessor+(encodePacket p).length+BinaryCounterMachine.borrowTime (b::bs) 0)+1 by omega,
        Function.iterate_succ_apply]
      change advance^[readTime ps i.predecessor+(encodePacket p).length+BinaryCounterMachine.borrowTime (b::bs) 0]
        (TM2.step program (configuration (some .check) v ((b::bs).map Symbol.bit) [] (encodePacket p++encodeCache ps)))=_
      rw [check_positive v (b::bs) (by simp) _ hc,Function.iterate_add_apply,hcounter,
        Function.iterate_add_apply,skip_iterate]
      exact ih i.predecessor (some .endPacket)

/-- Internally derived bound in actual encoded cache size and index width.
There is no desired total-cost premise or hidden packet-size constant. -/
theorem readTime_bound (ps : List WordIntegerPacket) (i : BinaryIndex) :
    readTime ps i≤(2*i.bits.length+3)*ps.length+2*(encodeCache ps).length+3 := by
  induction ps generalizing i with
  | nil => simp only [readTime,encodeCache,List.length_nil,Nat.mul_zero,Nat.zero_add];omega
  | cons p ps ih =>
    cases hb : i.bits with
    | nil =>
      simp only [readTime,hb,List.length_nil,encodeCache,List.length_append,List.length_cons,Nat.mul_zero,Nat.zero_add]
      omega
    | cons b bs =>
      have hs:=BinaryCounterMachine.borrowTime_bound i.bits 0
      have hw:=i.predecessor_width
      have hm:=Nat.mul_le_mul_right ps.length (show 2*i.predecessor.bits.length+3≤2*i.bits.length+3 by omega)
      have ht:readTime ps i.predecessor≤(2*i.bits.length+3)*ps.length+2*(encodeCache ps).length+3 :=
        (ih i.predecessor).trans (Nat.add_le_add_right (Nat.add_le_add_right hm _) _)
      simp only [readTime,hb,encodeCache,List.length_append,List.length_cons]
      simp only [hb,List.length_cons,Nat.add_zero] at hs ht ⊢
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at ht ⊢
      omega

/-- Full variable-length packet selection and frame copy in one official
finite TM2 execution. The actual cache bit/symbol data are scanned in place. -/
def readRun (ps : List WordIntegerPacket) (i : BinaryIndex) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .check) none (i.bits.map Symbol.bit) [] (encodeCache ps))
      (some (terminal ps i)) ((2*i.bits.length+3)*ps.length+2*(encodeCache ps).length+3) :=
  ⟨⟨readTime ps i,read_iterate ps i none⟩,readTime_bound ps i⟩

theorem readRun_steps (ps : List WordIntegerPacket) (i : BinaryIndex) : (readRun ps i).steps=readTime ps i := rfl

theorem terminal_label (ps : List WordIntegerPacket) (i : BinaryIndex) : (terminal ps i).l=none := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih =>
    cases hb : i.bits with
    | nil => simp only [terminal,hb,configuration,PacketStackPermutation.configuration]
    | cons b bs => simpa only [terminal,hb] using ih i.predecessor

theorem terminal_halts (ps : List WordIntegerPacket) (i : BinaryIndex) : TM2.step program (terminal ps i)=none := by
  have hl:=terminal_label ps i
  cases ht : terminal ps i with
  | mk l v S =>
    rw [ht] at hl
    change l=none at hl
    subst l
    rfl

theorem read_mem_eval (ps : List WordIntegerPacket) (i : BinaryIndex) :
    terminal ps i∈StateTransition.eval (TM2.step program)
      (configuration (some .check) none (i.bits.map Symbol.bit) [] (encodeCache ps)) :=
  evalsTo_terminal_mem_eval (readRun ps i).toEvalsTo (terminal_halts ps i)

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Option Symbol)=45 := by decide

theorem statement_depth (q : Label) : statementDepth (program q)≤7 := by
  cases q with
  | counter q =>
    rw [program,TM2Subroutine.redirect_statementDepth]
    exact PacketCounterLift.statement_depth q
  | skip =>
    rw [program,TM2Subroutine.redirect_statementDepth,skip_statement_depth]
    decide
  | copy q =>
    rw [program,TM2Subroutine.redirect_statementDepth]
    exact (copy_statement_depth q).trans (by decide)
  | check => simp only [program,statementDepth];omega
  | done => decide

theorem readRun_steps_height (ps : List WordIntegerPacket) (i : BinaryIndex) (B : ℕ)
    (h : ∀ p∈ps,IntegerPacketHeight p.decode B) :
    (readRun ps i).steps≤(2*i.bits.length+10*B+31)*ps.length+3 := by
  have hs:=(readRun ps i).steps_le_m
  have hc:=encodeCache_length_height ps B h
  nlinarith

end CircuitRecursion.PacketRecordMachine
