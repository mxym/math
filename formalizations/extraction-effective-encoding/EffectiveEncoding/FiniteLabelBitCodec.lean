import EffectiveEncoding.FixedWidthBinaryFields

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- A deliberately coarse positive width, polynomial in physical wires and
fixed library size. Every actual wire and label index fits internally. -/
def labelFieldWidth (m wires : ℕ) : ℕ := wires+m+1

structure BinaryLabelResult (m wires : ℕ) where
  bits : List Bool
  first : BinaryFieldResult (labelFieldWidth m wires)
  second : BinaryFieldResult (labelFieldWidth m wires)
  copyTrace : ListAssemblyTrace

/-- False tags a single; true tags a CNOT. Actual fields and copied output
are stored once, with no Nat.bits or rational data adapter. -/
def binaryLabelProgram {m wires : ℕ} : LabelGate m wires → BinaryLabelResult m wires
  | .single wire label =>
    let first:=binaryFieldProgram (labelFieldWidth m wires) wire.val
    let second:=binaryFieldProgram (labelFieldWidth m wires) label.val
    let output:=listAppendProgram first.output.bits.toList second.output.bits.toList
    ⟨false::output.value,first,second,output.trace⟩
  | .cnot c t h =>
    let first:=binaryFieldProgram (labelFieldWidth m wires) c.val
    let second:=binaryFieldProgram (labelFieldWidth m wires) t.val
    let output:=listAppendProgram first.output.bits.toList second.output.bits.toList
    ⟨true::output.value,first,second,output.trace⟩

/-- Actual prefix decoder. Its Nat interpretation/bounds/control execution
cost is not assigned by the encoder's primitive-action trace. -/
def readBinaryLabel (m wires : ℕ) : List Bool → Option (LabelGate m wires×List Bool)
  | [] => none
  | tag::bits => do
    let (first,rest)←takeBoolField (labelFieldWidth m wires) bits
    let (second,tail)←takeBoolField (labelFieldWidth m wires) rest
    let a:=binaryWordValue first
    let b:=binaryWordValue second
    if ha : a<wires then
      if tag then
        if hb : b<wires then
          if hab : a≠b then
            pure (.cnot ⟨a,ha⟩ ⟨b,hb⟩ (fun he => hab (congrArg Fin.val he)),tail)
          else none
        else none
      else if hb : b<m then pure (.single ⟨a,ha⟩ ⟨b,hb⟩,tail) else none
    else none

/-- Exact gate and suffix, including the original CNOT distinctness proof
up to proof irrelevance. All field width premises follow from Fin data. -/
theorem readBinaryLabel_roundtrip {m wires : ℕ} (g : LabelGate m wires) (tail : List Bool) :
    readBinaryLabel m wires ((binaryLabelProgram g).bits++tail)=some (g,tail) := by
  cases g with
  | single wire label =>
    have hw : wire.val<labelFieldWidth m wires := by unfold labelFieldWidth;omega
    have hl : label.val<labelFieldWidth m wires := by unfold labelFieldWidth;omega
    have hwp : wire.val<2^labelFieldWidth m wires := hw.trans (Nat.lt_two_pow_self)
    have hlp : label.val<2^labelFieldWidth m wires := hl.trans (Nat.lt_two_pow_self)
    simp [binaryLabelProgram,listAppendProgram_value,List.append_assoc,readBinaryLabel,
      takeBoolField_binaryField,binaryFieldProgram_value _ _ hwp,binaryFieldProgram_value _ _ hlp,
      wire.isLt,label.isLt]

  | cnot c t hct =>
    have hc : c.val<labelFieldWidth m wires := by unfold labelFieldWidth;omega
    have ht : t.val<labelFieldWidth m wires := by unfold labelFieldWidth;omega
    have hcp : c.val<2^labelFieldWidth m wires := hc.trans (Nat.lt_two_pow_self)
    have htp : t.val<2^labelFieldWidth m wires := ht.trans (Nat.lt_two_pow_self)
    have hne : c.val≠t.val := fun he => hct (Fin.ext he)
    simp [binaryLabelProgram,listAppendProgram_value,List.append_assoc,readBinaryLabel,
      takeBoolField_binaryField,binaryFieldProgram_value _ _ hcp,binaryFieldProgram_value _ _ htp,
      c.isLt,t.isLt,hne]



theorem binaryLabelProgram_length {m wires : ℕ} (g : LabelGate m wires) :
    (binaryLabelProgram g).bits.length=2*labelFieldWidth m wires+1 := by
  cases g <;> simp only [binaryLabelProgram,listAppendProgram_value,List.length_cons,List.length_append,
    binaryFieldProgram_length] <;> omega



def BinaryLabelResult.actions {m wires : ℕ} (r : BinaryLabelResult m wires) : ℕ :=
  r.first.actions+r.second.actions+r.copyTrace.actions+2


theorem binaryLabelProgram_actions {m wires : ℕ} (g : LabelGate m wires) :
    (binaryLabelProgram g).actions≤75*(labelFieldWidth m wires+1)^2 := by
  cases g with
  | single wire label =>
    have h1:=binaryFieldProgram_actions (labelFieldWidth m wires) wire.val (by unfold labelFieldWidth;omega)
    have h2:=binaryFieldProgram_actions (labelFieldWidth m wires) label.val (by unfold labelFieldWidth;omega)
    have hl : (binaryFieldProgram (labelFieldWidth m wires) wire.val).output.bits.toList.length=labelFieldWidth m wires :=
      (binaryFieldProgram (labelFieldWidth m wires) wire.val).output.bits.2
    simp only [binaryLabelProgram,BinaryLabelResult.actions,listAppendProgram_actions,hl]
    nlinarith
  | cnot c t hct =>
    have h1:=binaryFieldProgram_actions (labelFieldWidth m wires) c.val (by unfold labelFieldWidth;omega)
    have h2:=binaryFieldProgram_actions (labelFieldWidth m wires) t.val (by unfold labelFieldWidth;omega)
    have hl : (binaryFieldProgram (labelFieldWidth m wires) c.val).output.bits.toList.length=labelFieldWidth m wires :=
      (binaryFieldProgram (labelFieldWidth m wires) c.val).output.bits.2
    simp only [binaryLabelProgram,BinaryLabelResult.actions,listAppendProgram_actions,hl]
    nlinarith

end EffectiveEncoding
