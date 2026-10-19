import CircuitNumerical.PacketSerializerCheck
import CircuitNumerical.NativeQueryCheck

namespace CircuitRecursion.PacketMachineFixtures

open Turing PacketFraming

set_option maxRecDepth 2048

/-- Two small genuinely typed native packets with different signs/widths. -/
def raw0 : RawPacket := ⟨⟨false,[true]⟩,⟨false,[]⟩,⟨true,[true]⟩,⟨false,[false,true]⟩,[true]⟩
def raw1 : RawPacket := ⟨⟨false,[true,true]⟩,⟨true,[false,true]⟩,⟨false,[]⟩,⟨true,[true]⟩,[false,true]⟩

theorem valid0 : raw0.Valid := by
  refine ⟨?_,BinaryWordCanonical.one,by decide⟩
  intro i
  fin_cases i
  · exact ⟨.one,by decide⟩
  · exact ⟨.nil,by decide⟩
  · exact ⟨.one,by decide⟩
  · exact ⟨.prepend false true [] .one,by decide⟩

theorem valid1 : raw1.Valid := by
  refine ⟨?_,BinaryWordCanonical.prepend false true [] .one,by decide⟩
  intro i
  fin_cases i
  · exact ⟨.prepend true true [] .one,by decide⟩
  · exact ⟨.prepend false true [] .one,by decide⟩
  · exact ⟨.nil,by decide⟩
  · exact ⟨.one,by decide⟩

def packet0 : WordIntegerPacket := raw0.toWord valid0
def packet1 : WordIntegerPacket := raw1.toWord valid1
def index0 : BinaryIndex := ⟨[],.nil⟩
def index1 : BinaryIndex := ⟨[true],.one⟩

def oldIndex : List Symbol := [.field,.bit true,.endPacket]
def oldScratch : List Symbol := [.endPacket,.field]
def oldCache : List Symbol := [.bit false,.field,.endPacket,.bit true]
def queryTail : List Symbol := [.endPacket,.bit false,.field,.bit true]
def oldMemory : NativeQueryMachine.Memory := ((true,false,true,false),some .endPacket,true)

def oldWords : NativeQueryMachine.WordStack → List Bool
  | .scratch => [false,true]
  | .numerator .n0 => [true,false,true]
  | .numerator .n1 => [false]
  | .numerator .n2 => [true,true]
  | .numerator .n3 => [false,false]
  | .denominator => [true,false,true,false]

def packetFlags (p : WordIntegerPacket) : PacketFieldMachine.Flags :=
  ((p.numerators.get 0).negative,(p.numerators.get 1).negative,
    (p.numerators.get 2).negative,(p.numerators.get 3).negative)

def packetWords (p : WordIntegerPacket) : NativeQueryMachine.WordStack → List Bool
  | .scratch => []
  | .numerator .n0 => (p.numerators.get 0).bits
  | .numerator .n1 => (p.numerators.get 1).bits
  | .numerator .n2 => (p.numerators.get 2).bits
  | .numerator .n3 => (p.numerators.get 3).bits
  | .denominator => p.denominator

/-- Expected native terminal is specified directly from literal packet data,
not by NativeQueryMachine.terminal or its proof-side terminal recursion. -/
def expectedNative (master suffix queries : List Symbol) (p : WordIntegerPacket) : NativeQueryMachine.Configuration :=
  NativeQueryMachine.configuration none (packetFlags p,none,true)
    (PacketQueryMachine.stackData [] [] suffix master queries) (packetWords p)

def nativeStacks : List NativeQueryMachine.Stack :=
  [.inl (.inl (.inl .left)),.inl (.inl (.inl .right)),.inl (.inl (.inl .work)),
    .inl (.inl (.inr ())),.inl (.inr ()),.inr .scratch,.inr (.numerator .n0),.inr (.numerator .n1),
    .inr (.numerator .n2),.inr (.numerator .n3),.inr .denominator]

theorem nativeStacks_complete (k : NativeQueryMachine.Stack) : k∈nativeStacks := by
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> simp [nativeStacks]
      | inr k => cases k;simp [nativeStacks]
    | inr k => cases k;simp [nativeStacks]
  | inr k => cases k with
    | scratch | denominator => simp [nativeStacks]
    | numerator q => cases q <;> simp [nativeStacks]

instance nativeAlphabetDecidableEq (k : NativeQueryMachine.Stack) : DecidableEq (NativeQueryMachine.Alphabet k) := by
  cases k <;> infer_instance

def sameNative {Λ : Type*} [DecidableEq Λ]
    (a b : TM2.Cfg NativeQueryMachine.Alphabet Λ NativeQueryMachine.Memory) : Bool :=
  decide (a.l=b.l) && decide (a.var=b.var) && nativeStacks.all (fun k => decide (a.stk k=b.stk k))

/-- Test runner only: external fuel/count are not registers of the tested
TM2 program. Every transition is the official supplied TM2.step function. -/
def execute {C : Type*} (step : C → Option C) (stopped : C → Bool) : ℕ → ℕ → C → Option (ℕ×C)
  | 0,n,c => if stopped c then some (n,c) else none
  | fuel+1,n,c => if stopped c then some (n,c) else
      match step c with | none => none | some d => execute step stopped fuel (n+1) d

def assertNative (name : String) (c expected : NativeQueryMachine.Configuration) (steps : ℕ) : IO Unit := do
  match execute (TM2.step NativeQueryMachine.program) (fun c => c.l.isNone) 512 0 c with
  | none => throw (IO.userError ("MACHINE_FIXTURE_FAIL "++name++" no halt"))
  | some (actual,result) =>
    if actual != steps || !(sameNative result expected) then
      throw (IO.userError s!"MACHINE_FIXTURE_FAIL {name} steps={actual} expected={steps} terminal={sameNative result expected}")
    IO.println s!"MACHINE_FIXTURE_PASS {name} steps={actual} exact_terminal=true all_stacks=11"

#eval assertNative "native_one_index0_old_data" (NativeQueryMachine.initial [packet0] index0 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords) (expectedNative (encodeCache [packet0]) [] queryTail packet0) 119

#eval assertNative "native_two_index0_old_data" (NativeQueryMachine.initial [packet0,packet1] index0 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords)
  (expectedNative (encodeCache [packet0,packet1]) (encodeCache [packet1]) queryTail packet0) 151

#eval assertNative "native_two_index1_old_data" (NativeQueryMachine.initial [packet0,packet1] index1 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords) (expectedNative (encodeCache [packet0,packet1]) [] queryTail packet1) 178

abbrev DriverLabel := (Bool×NativeQueryMachine.Label)⊕Unit
instance driverDecidableEq : DecidableEq DriverLabel := by
  letI : DecidableEq NativeQueryMachine.Label := inferInstance
  exact inferInstance

abbrev DriverConfiguration := TM2.Cfg NativeQueryMachine.Alphabet DriverLabel NativeQueryMachine.Memory

def driverEmbed (second : Bool) (q : NativeQueryMachine.Label) : DriverLabel := .inl (second,q)
def driverReturn (second : Bool) (_ : NativeQueryMachine.Memory) : DriverLabel :=
  if second then .inr () else driverEmbed true (.inl .scratch)

def driverProgram : DriverLabel → TM2.Stmt NativeQueryMachine.Alphabet DriverLabel NativeQueryMachine.Memory
  | .inl (second,q) => TM2Subroutine.redirect (driverEmbed second) (driverReturn second) (NativeQueryMachine.program q)
  | .inr _ => .halt

def assertTwoNative (name : String) (first second : BinaryIndex) (firstPacket secondPacket : WordIntegerPacket)
    (firstSuffix : List Symbol) (firstSteps totalSteps : ℕ) : IO Unit := do
  let tail:=PacketQueryMachine.queryCode second.bits++queryTail
  let source:=NativeQueryMachine.initial [packet0,packet1] first oldMemory oldIndex oldScratch oldCache tail oldWords
  let start:=TM2Subroutine.liftConfiguration (driverEmbed false) (driverReturn false) source
  let firstCheckpoint:=(fun x : Option DriverConfiguration => x.bind (TM2.step driverProgram))^[firstSteps] (some start)
  let expectedFirst:=expectedNative (encodeCache [packet0,packet1]) firstSuffix tail firstPacket
  let firstCfg:DriverConfiguration:=⟨some (driverEmbed true (.inl .scratch)),expectedFirst.var,expectedFirst.stk⟩
  let prefixOK:=match firstCheckpoint with | some c => sameNative c firstCfg | none => false
  let expectedLast:=expectedNative (encodeCache [packet0,packet1]) (if second.bits=[] then encodeCache [packet1] else []) queryTail secondPacket
  let finalCfg:DriverConfiguration:=⟨none,expectedLast.var,expectedLast.stk⟩
  match execute (TM2.step driverProgram) (fun c => c.l.isNone) 768 0 start with
  | none => throw (IO.userError ("MACHINE_FIXTURE_FAIL "++name++" no halt"))
  | some (actual,result) =>
    if !prefixOK || actual != totalSteps || !(sameNative result finalCfg) then
      throw (IO.userError s!"MACHINE_FIXTURE_FAIL {name} steps={actual} expected={totalSteps} firstCheckpoint={prefixOK} terminal={sameNative result finalCfg}")
    IO.println s!"MACHINE_FIXTURE_PASS {name} steps={actual} exact_terminal=true exact_first_prefix=true all_stacks=11"

#eval assertTwoNative "native_actual_two_queries_0_then_1" index0 index1 packet0 packet1 (encodeCache [packet1]) 151 328
#eval assertTwoNative "native_actual_two_queries_1_then_0" index1 index0 packet1 packet0 [] 178 314

instance fieldAlphabetDecidableEq (k : PacketFieldMachine.Stack) : DecidableEq (PacketFieldMachine.Alphabet k) := by
  cases k <;> infer_instance

def fieldStacks : List PacketFieldMachine.Stack :=
  [.input,.scratch,.numerator .n0,.numerator .n1,.numerator .n2,.numerator .n3,.denominator]

theorem fieldStacks_complete (k : PacketFieldMachine.Stack) : k∈fieldStacks := by
  cases k with
  | input | scratch | denominator => simp [fieldStacks]
  | numerator q => cases q <;> simp [fieldStacks]

def sameFields {Λ : Type*} [DecidableEq Λ]
    (a b : TM2.Cfg PacketFieldMachine.Alphabet Λ PacketFieldMachine.Memory) : Bool :=
  decide (a.l=b.l) && decide (a.var=b.var) && fieldStacks.all (fun k => decide (a.stk k=b.stk k))

def assertSerializer : IO Unit := do
  let source:=PacketSerializerMachine.configuration (some .clearScratch) (packetFlags packet0) (some (.bit true)) false
    queryTail [false,true,false] (PacketFieldMachine.outputFields raw0) packet0.denominator
  let expected:PacketSerializerMachine.Configuration:=⟨none,(packetFlags packet0,none,false),
    PacketFieldMachine.stackData (encodePacket packet0++queryTail) [] (fun _ => []) []⟩
  match execute (TM2.step PacketSerializerMachine.program) (fun c => c.l.isNone) 128 0 source with
  | none => throw (IO.userError "MACHINE_FIXTURE_FAIL serializer no halt")
  | some (actual,result) =>
    if actual != 33 || !(sameFields result expected) then
      throw (IO.userError s!"MACHINE_FIXTURE_FAIL serializer steps={actual} terminal={sameFields result expected}")
    IO.println s!"MACHINE_FIXTURE_PASS serializer steps={actual} exact_terminal=true all_stacks=7"

#eval assertSerializer

def assertCodec : IO Unit := do
  let source:=PacketCodecMachine.initial raw1 queryTail
  let expected:PacketCodecMachine.Configuration:=⟨none,(packetFlags packet1,none,true),
    PacketFieldMachine.stackData (encodePacket packet1++queryTail) [] (fun _ => []) []⟩
  match execute (TM2.step PacketCodecMachine.program) (fun c => c.l.isNone) 128 0 source with
  | none => throw (IO.userError "MACHINE_FIXTURE_FAIL codec no halt")
  | some (actual,result) =>
    if actual != 63 || !(sameFields result expected) then
      throw (IO.userError s!"MACHINE_FIXTURE_FAIL codec steps={actual} terminal={sameFields result expected}")
    IO.println s!"MACHINE_FIXTURE_PASS codec steps={actual} exact_terminal=true all_stacks=7"

#eval assertCodec

end CircuitRecursion.PacketMachineFixtures
