import CircuitNumerical.PacketSerializerRoundtrip

namespace CircuitRecursion.PacketCodecMachine

open Turing PacketFraming

abbrev Alphabet := PacketFieldMachine.Alphabet
abbrev Memory := PacketFieldMachine.Memory
abbrev Label := PacketFieldMachine.Label ⊕ (PacketSerializerMachine.Label⊕Unit)
abbrev Configuration := TM2.Cfg Alphabet Label Memory

def parserEmbed (q : PacketFieldMachine.Label) : Label := .inl q
def parserReturn (_ : Memory) : Label := .inr (.inl .clearScratch)
def serializerEmbed (q : PacketSerializerMachine.Label) : Label := .inr (.inl q)
def serializerReturn (_ : Memory) : Label := .inr (.inr ())

/-- Parser and serializer operate on the very same physical heterogeneous
seven stacks. Source parser halt jumps directly to actual serializer entry. -/
def program : Label → TM2.Stmt Alphabet Label Memory
  | .inl q => TM2Subroutine.redirect parserEmbed parserReturn (PacketFieldMachine.program q)
  | .inr (.inl q) => TM2Subroutine.redirect serializerEmbed serializerReturn (PacketSerializerMachine.program q)
  | .inr (.inr _) => .halt

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

def initial (r : RawPacket) (rest : List Symbol) : Configuration :=
  TM2Subroutine.liftConfiguration parserEmbed parserReturn
    (PacketFieldMachine.configuration (some (.sign .n0)) PacketFieldMachine.emptyFlags none false
      (encodeRaw r++rest) [] PacketFieldMachine.emptyFields [])

def intermediate (r : RawPacket) (rest : List Symbol) : Configuration :=
  TM2Subroutine.liftConfiguration parserEmbed parserReturn (PacketFieldMachine.terminal r rest)

def terminal (r : RawPacket) (rest : List Symbol) : Configuration :=
  let c:=PacketSerializerMachine.terminal r rest true
  ⟨none,c.var,c.stk⟩

def codecTime (r : RawPacket) : ℕ := PacketFieldMachine.parseTime r+PacketSerializerMachine.serializeTime r []+1

def parserCall (r : RawPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program) (initial r rest) (some (intermediate r rest))
      (PacketFieldMachine.parseTime r) :=
  TM2Subroutine.redirectedRun parserEmbed parserReturn PacketFieldMachine.program program (fun _ => rfl)
    (PacketFieldMachine.parseRun r rest)

theorem parser_to_serializer (r : RawPacket) (rest : List Symbol) :
    intermediate r rest=TM2Subroutine.liftConfiguration serializerEmbed serializerReturn
      (PacketSerializerMachine.configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) none true rest []
        (PacketFieldMachine.outputFields r) r.denominator) := rfl

def serializerCall (r : RawPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn
        (PacketSerializerMachine.configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) none true rest []
          (PacketFieldMachine.outputFields r) r.denominator))
      (some (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn (PacketSerializerMachine.terminal r rest true)))
      (PacketSerializerMachine.serializeTime r []) :=
  TM2Subroutine.redirectedRun serializerEmbed serializerReturn PacketSerializerMachine.program program (fun _ => rfl)
    (PacketSerializerMachine.serializeRun r rest [] none true)

theorem finish_step (r : RawPacket) (rest : List Symbol) :
    TM2.step program (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn (PacketSerializerMachine.terminal r rest true))=
      some (terminal r rest) := rfl

/-- Full physical parse/serialize roundtrip in one finite program, with
intermediate native bits and no host conversion or procedure boundary. -/
def codecRun (r : RawPacket) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program) (initial r rest) (some (terminal r rest)) (codecTime r) :=
  ⟨⟨codecTime r,by
    change advance^[codecTime r] (some (initial r rest))=_
    have h₁ : advance^[PacketFieldMachine.parseTime r] (some (initial r rest))=some (intermediate r rest) :=
      (parserCall r rest).evals_in_steps
    have h₂ : advance^[PacketSerializerMachine.serializeTime r []]
        (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn
          (PacketSerializerMachine.configuration (some .clearScratch) (PacketFieldMachine.outputFlags r) none true rest []
            (PacketFieldMachine.outputFields r) r.denominator) |> some)=
      some (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn (PacketSerializerMachine.terminal r rest true)) :=
      (serializerCall r rest).evals_in_steps
    have hm : advance^[PacketSerializerMachine.serializeTime r []+PacketFieldMachine.parseTime r] (some (initial r rest))=
        some (TM2Subroutine.liftConfiguration serializerEmbed serializerReturn (PacketSerializerMachine.terminal r rest true)) := by
      rw [Function.iterate_add_apply,h₁,parser_to_serializer]
      exact h₂
    rw [show codecTime r=1+(PacketSerializerMachine.serializeTime r []+PacketFieldMachine.parseTime r) by unfold codecTime;omega,
      Function.iterate_add_apply,hm]
    exact finish_step r rest⟩,le_rfl⟩

theorem codecRun_steps (r : RawPacket) (rest : List Symbol) : (codecRun r rest).steps=codecTime r := rfl

theorem codecTime_encoded_length (r : RawPacket) : codecTime r+1=4*(encodeRaw r).length := by
  have hp:=PacketFieldMachine.parseTime_encoded_length r
  have hs:=PacketSerializerMachine.serializeTime_encoded_length r []
  unfold codecTime
  simp only [List.length_nil] at hs
  omega

theorem codecRun_steps_height (p : WordIntegerPacket) (rest : List Symbol) (B : ℕ) (h : IntegerPacketHeight p.decode B) :
    (codecRun (rawPacket p) rest).steps≤20*B+55 := by
  rw [codecRun_steps]
  have ht:=codecTime_encoded_length (rawPacket p)
  have hl:=encodePacket_length_height p B h
  change (encodeRaw (rawPacket p)).length≤_ at hl
  omega

def observedNative (c : Configuration) : RawPacket :=
  ⟨⟨c.var.1.1,c.stk (.numerator .n0)⟩,⟨c.var.1.2.1,c.stk (.numerator .n1)⟩,
    ⟨c.var.1.2.2.1,c.stk (.numerator .n2)⟩,⟨c.var.1.2.2.2,c.stk (.numerator .n3)⟩,c.stk .denominator⟩

theorem intermediate_native_exact (r : RawPacket) (rest : List Symbol) : observedNative (intermediate r rest)=r := rfl

theorem terminal_encoded_exact (r : RawPacket) (rest : List Symbol) : (terminal r rest).stk .input=encodeRaw r++rest := rfl

theorem terminal_numerators_empty (r : RawPacket) (rest : List Symbol) (q : PacketFieldMachine.Coordinate) :
    (terminal r rest).stk (.numerator q)=[] := rfl

theorem terminal_denominator_empty (r : RawPacket) (rest : List Symbol) : (terminal r rest).stk .denominator=[] := rfl

theorem terminal_scratch_empty (r : RawPacket) (rest : List Symbol) : (terminal r rest).stk .scratch=[] := rfl

theorem terminal_halts (r : RawPacket) (rest : List Symbol) : TM2.step program (terminal r rest)=none := rfl

theorem codec_mem_eval (r : RawPacket) (rest : List Symbol) :
    terminal r rest∈StateTransition.eval (TM2.step program) (initial r rest) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (codecRun r rest).toEvalsTo (terminal_halts r rest)

theorem program_supports : TM2.Supports program Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem running_control_card : Fintype.card (Label×Memory)=5600 := by
  rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_sum,Fintype.card_unit,PacketFieldMachine.memory_card]
  have hp : Fintype.card PacketFieldMachine.Label=14 := by decide
  have hs : Fintype.card PacketSerializerMachine.Label=20 := by decide
  rw [hp,hs]

theorem statement_depth (q : Label) : ListAssemblyMachine.statementDepth (program q)≤5 := by
  cases q with
  | inl q =>
    rw [program,TM2Subroutine.redirect_statementDepth]
    exact PacketFieldMachine.statement_depth q
  | inr q => cases q with
    | inl q =>
      rw [program,TM2Subroutine.redirect_statementDepth]
      exact (PacketSerializerMachine.statement_depth q).trans (by decide)
    | inr q => simp only [program,ListAssemblyMachine.statementDepth];omega

end CircuitRecursion.PacketCodecMachine
