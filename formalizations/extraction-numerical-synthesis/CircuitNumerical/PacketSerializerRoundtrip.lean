import CircuitNumerical.PacketSerializerRuns

namespace CircuitRecursion.PacketSerializerMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

def freshTime (r : RawPacket) : ℕ :=
  2*r.n0.bits.length+2*r.n1.bits.length+2*r.n2.bits.length+2*r.n3.bits.length+2*r.denominator.length+19

def serializeTime (r : RawPacket) (scratch : List Bool) : ℕ := scratch.length+1+freshTime r

def terminal (r : RawPacket) (out : List Symbol) (ok : Bool) : Configuration :=
  configuration none (PacketFieldMachine.outputFlags r) none ok (encodeRaw r++out) [] PacketFieldMachine.emptyFields []

theorem fresh_iterate (r : RawPacket) (out : List Symbol) (ok : Bool) :
    advance^[freshTime r]
      (some (configuration (some .start) (PacketFieldMachine.outputFlags r) none ok out []
        (PacketFieldMachine.outputFields r) r.denominator))=some (terminal r out ok) := by
  let f3:=Function.update (PacketFieldMachine.outputFields r) .n3 []
  let f2:=Function.update f3 .n2 []
  let f1:=Function.update f2 .n1 []
  rw [show freshTime r=
    ((2*r.n0.bits.length+4)+(2*r.n1.bits.length+4)+(2*r.n2.bits.length+4)+(2*r.n3.bits.length+4)+
      (2*r.denominator.length+2))+1 by unfold freshTime;omega,Function.iterate_succ_apply]
  change advance^[(2*r.n0.bits.length+4)+(2*r.n1.bits.length+4)+(2*r.n2.bits.length+4)+(2*r.n3.bits.length+4)+
      (2*r.denominator.length+2)]
    (TM2.step program (configuration (some .start) (PacketFieldMachine.outputFlags r) none ok out []
      (PacketFieldMachine.outputFields r) r.denominator))=_
  rw [start_step,Function.iterate_add_apply,denominator_iterate]
  rw [Function.iterate_add_apply,
    show 2*r.n3.bits.length+4=2*(PacketFieldMachine.outputFields r .n3).length+4 by rfl,numerator_iterate]
  simp only [next]
  rw [Function.iterate_add_apply,show 2*r.n2.bits.length+4=2*(f3 .n2).length+4 by rfl,numerator_iterate]
  simp only [next]
  rw [Function.iterate_add_apply,show 2*r.n1.bits.length+4=2*(f2 .n1).length+4 by rfl,numerator_iterate]
  simp only [next]
  rw [show 2*r.n0.bits.length+4=2*(f1 .n0).length+4 by rfl,numerator_iterate]
  simp only [next]
  apply congrArg some
  unfold terminal configuration
  congr 1
  funext k
  cases k with
  | input => simp only [PacketFieldMachine.stackData,encodeRaw,payload,List.append_assoc,List.singleton_append];rfl
  | scratch | denominator => rfl
  | numerator q => cases q <;> rfl

theorem serialize_iterate (r : RawPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    advance^[serializeTime r scratch]
      (some (configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) v ok out scratch
        (PacketFieldMachine.outputFields r) r.denominator))=some (terminal r out ok) := by
  unfold serializeTime
  rw [Nat.add_comm,Function.iterate_add_apply,clear_iterate,fresh_iterate]

/-- Actual native Bool packet to framed Symbol prefix. All original five
word fields are consumed, prior scratch is really cleared, and the old
Symbol output suffix is retained after the new exact frame. -/
def serializeRun (r : RawPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) v ok out scratch
        (PacketFieldMachine.outputFields r) r.denominator)
      (some (terminal r out ok)) (serializeTime r scratch) :=
  ⟨⟨serializeTime r scratch,serialize_iterate r out scratch v ok⟩,le_rfl⟩

theorem serializeRun_steps (r : RawPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    (serializeRun r out scratch v ok).steps=serializeTime r scratch := rfl

theorem serializeTime_encoded_length (r : RawPacket) (scratch : List Bool) :
    serializeTime r scratch=scratch.length+2*(encodeRaw r).length+2 := by
  rw [encodeRaw_length]
  unfold serializeTime freshTime
  omega

def serializePacketRun (p : WordIntegerPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some .clearScratch) (PacketFieldMachine.outputFlags (rawPacket p)) v ok out scratch
        (PacketFieldMachine.outputFields (rawPacket p)) p.denominator)
      (some (terminal (rawPacket p) out ok)) (serializeTime (rawPacket p) scratch) :=
  serializeRun (rawPacket p) out scratch v ok

theorem serializePacketRun_steps_height (p : WordIntegerPacket) (out : List Symbol) (scratch : List Bool)
    (v : Option Symbol) (ok : Bool) (B : ℕ) (h : IntegerPacketHeight p.decode B) :
    (serializePacketRun p out scratch v ok).steps≤scratch.length+10*B+30 := by
  change serializeTime (rawPacket p) scratch≤_
  rw [serializeTime_encoded_length]
  have hl:=encodePacket_length_height p B h
  change (encodeRaw (rawPacket p)).length≤_ at hl
  omega

theorem terminal_encoded (r : RawPacket) (out : List Symbol) (ok : Bool) :
    (terminal r out ok).stk .input=encodeRaw r++out := rfl

theorem terminal_empty_fields (r : RawPacket) (out : List Symbol) (ok : Bool) (q : Coordinate) :
    (terminal r out ok).stk (.numerator q)=[] := rfl

theorem terminal_empty_denominator (r : RawPacket) (out : List Symbol) (ok : Bool) :
    (terminal r out ok).stk .denominator=[] := rfl

theorem terminal_empty_scratch (r : RawPacket) (out : List Symbol) (ok : Bool) :
    (terminal r out ok).stk .scratch=[] := rfl

theorem serialized_decode (p : WordIntegerPacket) (out : List Symbol) (ok : Bool) :
    decodeRaw ((terminal (rawPacket p) out ok).stk .input)=some (rawPacket p,out) := decodeRaw_encodePacket p out

theorem terminal_halts (r : RawPacket) (out : List Symbol) (ok : Bool) : TM2.step program (terminal r out ok)=none := rfl

theorem serialize_mem_eval (r : RawPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    terminal r out ok∈StateTransition.eval (TM2.step program)
      (configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) v ok out scratch
        (PacketFieldMachine.outputFields r) r.denominator) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (serializeRun r out scratch v ok).toEvalsTo (terminal_halts r out ok)

/-- Actual literal CPS insertion; serialization does not execute a host
packet append and its original Bool payload is not preserved for free. -/
def serializeCall {Δ : Type*} (ret : Memory → Δ) (outer : Δ → TM2.Stmt Alphabet (Label⊕Δ) Memory)
    (r : RawPacket) (out : List Symbol) (scratch : List Bool) (v : Option Symbol) (ok : Bool) :
    StateTransition.EvalsToInTime (TM2.step (TM2Subroutine.splice program ret outer))
      (TM2Subroutine.liftConfiguration Sum.inl (fun m => Sum.inr (ret m))
        (configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) v ok out scratch
          (PacketFieldMachine.outputFields r) r.denominator))
      (some (TM2Subroutine.liftConfiguration Sum.inl (fun m => Sum.inr (ret m)) (terminal r out ok)))
      (serializeTime r scratch) := TM2Subroutine.spliceRun program ret outer (serializeRun r out scratch v ok)

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Memory)=3200 := by
  rw [Fintype.card_prod,PacketFieldMachine.memory_card]
  have hl : Fintype.card Label=20 := by decide
  rw [hl]

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤4 := by
  cases q <;> simp only [program,finish,ListAssemblyMachine.statementDepth] <;>
    first | omega | (rename_i q;cases q <;> simp only [ListAssemblyMachine.statementDepth] <;> omega)

end CircuitRecursion.PacketSerializerMachine
