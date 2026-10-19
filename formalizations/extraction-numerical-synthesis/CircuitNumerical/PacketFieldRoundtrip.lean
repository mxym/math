import CircuitNumerical.PacketFieldRuns

namespace CircuitRecursion.PacketFieldMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

def emptyFields : Coordinate → List Bool := fun _ => []
def emptyFlags : Flags := (false,false,false,false)

def outputFields (r : RawPacket) : Coordinate → List Bool
  | .n0 => r.n0.bits
  | .n1 => r.n1.bits
  | .n2 => r.n2.bits
  | .n3 => r.n3.bits

def outputFlags (r : RawPacket) : Flags := (r.n0.negative,r.n1.negative,r.n2.negative,r.n3.negative)

def terminal (r : RawPacket) (rest : List Symbol) : Configuration :=
  configuration none (outputFlags r) none true rest [] (outputFields r) r.denominator

/-- Proof-side transition index; there is no runtime natural clock. -/
def parseTime (r : RawPacket) : ℕ :=
  2*r.n0.bits.length+2*r.n1.bits.length+2*r.n2.bits.length+2*r.n3.bits.length+2*r.denominator.length+14

theorem parse_iterate (r : RawPacket) (rest : List Symbol) :
    advance^[parseTime r]
      (some (configuration (some (.sign .n0)) emptyFlags none false (encodeRaw r++rest) [] emptyFields []))=
      some (terminal r rest) := by
  simp only [encodeRaw,payload,List.append_assoc,List.singleton_append]
  rw [show parseTime r=
    ((2*r.n1.bits.length+3)+(2*r.n2.bits.length+3)+(2*r.n3.bits.length+3)+(2*r.denominator.length+2))+
      (2*r.n0.bits.length+3) by unfold parseTime;omega,
    Function.iterate_add_apply,signedField_iterate]
  simp only [next]
  rw [show (2*r.n1.bits.length+3)+(2*r.n2.bits.length+3)+(2*r.n3.bits.length+3)+(2*r.denominator.length+2)=
    ((2*r.n2.bits.length+3)+(2*r.n3.bits.length+3)+(2*r.denominator.length+2))+(2*r.n1.bits.length+3) by omega,
    Function.iterate_add_apply,signedField_iterate]
  simp only [next]
  rw [show (2*r.n2.bits.length+3)+(2*r.n3.bits.length+3)+(2*r.denominator.length+2)=
    ((2*r.n3.bits.length+3)+(2*r.denominator.length+2))+(2*r.n2.bits.length+3) by omega,
    Function.iterate_add_apply,signedField_iterate]
  simp only [next]
  rw [show (2*r.n3.bits.length+3)+(2*r.denominator.length+2)=
    (2*r.denominator.length+2)+(2*r.n3.bits.length+3) by omega,
    Function.iterate_add_apply,signedField_iterate]
  simp only [next]
  rw [denominator_iterate]
  apply congrArg some
  unfold terminal configuration
  congr 1
  funext k
  cases k with
  | input | scratch => rfl
  | denominator => simp only [stackData,List.append_nil]
  | numerator q => cases q <;> simp [stackData,outputFields,emptyFields,Function.update]

/-- Full actual field extraction into native Bool word stacks. Input suffix
is untouched and the accepted flag is set only after the final restoration. -/
def parseRun (r : RawPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.sign .n0)) emptyFlags none false (encodeRaw r++rest) [] emptyFields [])
      (some (terminal r rest)) (parseTime r) :=
  ⟨⟨parseTime r,parse_iterate r rest⟩,le_rfl⟩

theorem parseRun_steps (r : RawPacket) (rest : List Symbol) : (parseRun r rest).steps=parseTime r := rfl

theorem parseTime_encoded_length (r : RawPacket) : parseTime r+4=2*(encodeRaw r).length := by
  rw [encodeRaw_length]
  unfold parseTime
  omega

def parsePacketRun (p : WordIntegerPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.sign .n0)) emptyFlags none false (encodePacket p++rest) [] emptyFields [])
      (some (terminal (rawPacket p) rest)) (parseTime (rawPacket p)) := parseRun (rawPacket p) rest

theorem parsePacketRun_steps_height (p : WordIntegerPacket) (rest : List Symbol) (B : ℕ)
    (h : IntegerPacketHeight p.decode B) : (parsePacketRun p rest).steps≤10*B+24 := by
  have ht:=parseTime_encoded_length (rawPacket p)
  have hl:=encodePacket_length_height p B h
  change (encodeRaw (rawPacket p)).length≤_ at hl
  change parseTime (rawPacket p)≤_
  omega

/-- Reading the physical output representation, without Nat, Rat or
complex-number conversion. This observation does not charge record packaging. -/
def resultRaw (c : Configuration) : RawPacket :=
  ⟨⟨c.var.1.1,c.stk (.numerator .n0)⟩,⟨c.var.1.2.1,c.stk (.numerator .n1)⟩,
    ⟨c.var.1.2.2.1,c.stk (.numerator .n2)⟩,⟨c.var.1.2.2.2,c.stk (.numerator .n3)⟩,c.stk .denominator⟩

theorem resultRaw_terminal (r : RawPacket) (rest : List Symbol) : resultRaw (terminal r rest)=r := rfl

theorem terminal_input (r : RawPacket) (rest : List Symbol) : (terminal r rest).stk .input=rest := rfl

theorem terminal_scratch (r : RawPacket) (rest : List Symbol) : (terminal r rest).stk .scratch=[] := rfl

theorem terminal_accepted (r : RawPacket) (rest : List Symbol) : (terminal r rest).var.2.2=true := rfl

theorem terminal_halts (r : RawPacket) (rest : List Symbol) : TM2.step program (terminal r rest)=none := rfl

theorem parse_mem_eval (r : RawPacket) (rest : List Symbol) : terminal r rest∈StateTransition.eval (TM2.step program)
    (configuration (some (.sign .n0)) emptyFlags none false (encodeRaw r++rest) [] emptyFields []) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (parseRun r rest).toEvalsTo (terminal_halts r rest)

/-- Canonicality and positive denominator are inherited from the original
typed packet; this parser preserves exact fields, and performs no normalize. -/
theorem typed_result (p : WordIntegerPacket) (rest : List Symbol) :
    (resultRaw (terminal (rawPacket p) rest)).toWord (rawPacket_valid p)=p := rawPacket_toWord p

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem stack_card : Fintype.card Stack=7 := by decide

theorem memory_card : Fintype.card Memory=160 := by
  simp only [Memory,Flags,Fintype.card_prod,Fintype.card_bool,Fintype.card_option,symbol_card]

theorem running_control_card : Fintype.card (Label×Memory)=2240 := by
  rw [Fintype.card_prod,memory_card]
  have hl : Fintype.card Label=14 := by decide
  rw [hl]

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤5 := by
  cases q <;> simp only [program,ListAssemblyMachine.statementDepth] <;> omega

end CircuitRecursion.PacketFieldMachine
