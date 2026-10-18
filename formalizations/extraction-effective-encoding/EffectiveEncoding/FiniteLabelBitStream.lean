import EffectiveEncoding.FiniteLabelBitCodec

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

inductive BinaryStreamTrace (m wires : ℕ) where
  | stop
  | step : BinaryLabelResult m wires → ListAssemblyTrace → BinaryStreamTrace m wires → BinaryStreamTrace m wires

structure BinaryStreamResult (m wires : ℕ) where
  bits : List Bool
  trace : BinaryStreamTrace m wires

/-- False terminates a stream; true precedes one concrete gate encoding.
Each field program and output copy is executed once and retained. -/
def binaryLabelStream {m wires : ℕ} : List (LabelGate m wires) → BinaryStreamResult m wires
  | [] => ⟨[false],.stop⟩
  | g::gs =>
    let gate:=binaryLabelProgram g
    let tail:=binaryLabelStream gs
    let output:=listAppendProgram gate.bits tail.bits
    ⟨true::output.value,.step gate output.trace tail.trace⟩


def readBinaryLabelStreamFuel (m wires : ℕ) : ℕ → List Bool → Option (List (LabelGate m wires)×List Bool)
  | 0,_ => none
  | _+1,[] => none
  | _+1,false::tail => some ([],tail)
  | fuel+1,true::bits => do
    let (gate,rest)←readBinaryLabel m wires bits
    let (gates,tail)←readBinaryLabelStreamFuel m wires fuel rest
    pure (gate::gates,tail)

/-- Exact whole label stream and arbitrary unconsumed suffix. The caller's
fuel bound is discharged by the concrete automatic reader below. -/
theorem readBinaryLabelStreamFuel_roundtrip {m wires : ℕ} (gs : List (LabelGate m wires))
    (tail : List Bool) (fuel : ℕ) (h : gs.length<fuel) :
    readBinaryLabelStreamFuel m wires fuel ((binaryLabelStream gs).bits++tail)=some (gs,tail) := by
  induction gs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at h
    | succ fuel => rfl
  | cons g gs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have ht : gs.length<fuel := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using h
      simp [binaryLabelStream,listAppendProgram_value,List.append_assoc,readBinaryLabelStreamFuel,
        readBinaryLabel_roundtrip,ih fuel ht]


theorem binaryLabelStream_length {m wires : ℕ} (gs : List (LabelGate m wires)) :
    (binaryLabelStream gs).bits.length=gs.length*(2*labelFieldWidth m wires+2)+1 := by
  induction gs with
  | nil => simp [binaryLabelStream]
  | cons g gs ih =>
    simp only [binaryLabelStream,listAppendProgram_value,List.length_cons,List.length_append,
      binaryLabelProgram_length,ih]
    ring


def readBinaryLabelStream (m wires : ℕ) (bits : List Bool) : Option (List (LabelGate m wires)×List Bool) :=
  readBinaryLabelStreamFuel m wires (bits.length+1) bits


theorem readBinaryLabelStream_roundtrip {m wires : ℕ} (gs : List (LabelGate m wires)) (tail : List Bool) :
    readBinaryLabelStream m wires ((binaryLabelStream gs).bits++tail)=some (gs,tail) := by
  apply readBinaryLabelStreamFuel_roundtrip
  rw [List.length_append,binaryLabelStream_length]
  nlinarith


def deserializeLabelStream (m wires : ℕ) (bits : List Bool) : List (LabelGate m wires) :=
  ((readBinaryLabelStream m wires bits).map Prod.fst).getD []


theorem deserializeLabelStream_roundtrip {m wires : ℕ} (gs : List (LabelGate m wires)) :
    deserializeLabelStream m wires (binaryLabelStream gs).bits=gs := by
  have h:=readBinaryLabelStream_roundtrip gs []
  simpa only [List.append_nil,deserializeLabelStream,h,Option.map_some,Option.getD_some] using
    congrArg (fun x : Option (List (LabelGate m wires)×List Bool) => (x.map Prod.fst).getD []) h


def BinaryStreamTrace.actions {m wires : ℕ} : BinaryStreamTrace m wires → ℕ
  | .stop => 2
  | .step gate copy tail => gate.actions+copy.actions+tail.actions+2

/-- Actual retained count-word, fixed-digit, tag/list and output-copy
primitives. This does not charge decoder or general host control. -/
theorem binaryLabelStream_actions {m wires : ℕ} (gs : List (LabelGate m wires)) :
    (binaryLabelStream gs).trace.actions≤gs.length*(90*(labelFieldWidth m wires+1)^2)+2 := by
  induction gs with
  | nil => simp [binaryLabelStream,BinaryStreamTrace.actions]
  | cons g gs ih =>
    have hg:=binaryLabelProgram_actions g
    simp only [binaryLabelStream,BinaryStreamTrace.actions,listAppendProgram_actions,binaryLabelProgram_length]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    nlinarith

end EffectiveEncoding
