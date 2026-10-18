import EffectiveEncoding.FullyAssembledInputExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Real emitted labels; list and fixed output-record constructor actions
are specified below. Existing wire/label data are referenced, not bit-copied. -/
inductive WireLabelTrace (m : ℕ) where
  | done
  | emit : Fin m → WireLabelTrace m → WireLabelTrace m

structure WireLabelResult (m wires : ℕ) where
  word : List (LabelGate m wires)
  trace : WireLabelTrace m

/-- One forward list pass, constructing each fixed LabelGate.single once. -/
def wireLabelProgram {m wires : ℕ} (wire : Fin wires) : List (Fin m) → WireLabelResult m wires
  | [] => ⟨[],.done⟩
  | a::as =>
    let gate:=LabelGate.single wire a
    let tail:=wireLabelProgram wire as
    ⟨gate::tail.word,.emit a tail.trace⟩


theorem wireLabelProgram_word {m wires : ℕ} (wire : Fin wires) (xs : List (Fin m)) :
    (wireLabelProgram wire xs).word=wireLabels wire xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [wireLabelProgram,wireLabels,List.map_cons,ih]

/-- Explicit fixed-record/list-spine model. Payload Nat bits, arbitrary
provider work, general control and computing this projection are separate. -/
def WireLabelTrace.actions {m : ℕ} : WireLabelTrace m → ℕ
  | .done => 1
  | .emit _ t => t.actions+6


theorem wireLabelProgram_actions {m wires : ℕ} (wire : Fin wires) (xs : List (Fin m)) :
    (wireLabelProgram wire xs).trace.actions=6*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [wireLabelProgram,WireLabelTrace.actions,List.length_cons,ih]
    omega

inductive OuterLabelTrace (m : ℕ) where
  | empty
  | single : WireLabelTrace m → OuterLabelTrace m
  | cnot
  | joined : OuterLabelTrace m → OuterLabelTrace m → ListAssemblyTrace → ListAssemblyTrace → OuterLabelTrace m


def OuterLabelTrace.actions {m : ℕ} : OuterLabelTrace m → ℕ
  | .empty => 1
  | .single t => t.actions+2
  | .cnot => 2
  | .joined head tail wordCopy programCopy => head.actions+tail.actions+wordCopy.actions+programCopy.actions

structure MaterializedLabelRun (m wires L q : ℕ) where
  value : AssembledCompiledLabelRun m wires L q
  trace : OuterLabelTrace m

/-- The synthesis run and mapped label list are each evaluated once. -/
def materializeGate {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q) :
    GateCode wires → MaterializedLabelRun m wires L q
  | .single wire u =>
    let program:=synth u
    let output:=wireLabelProgram wire program.cached.program.program.word
    ⟨⟨output.word,[program]⟩,.single output.trace⟩
  | .cnot c t h => ⟨⟨[.cnot c t h],[]⟩,.cnot⟩

/-- Actual output-label and retained-program list copies, executed once.
Their concrete traces remain beside the emitted word and target records. -/
def materializeWord {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q) :
    WordCode wires → MaterializedLabelRun m wires L q
  | [] => ⟨⟨[],[]⟩,.empty⟩
  | g::gs =>
    let gate:=materializeGate synth g
    let tail:=materializeWord synth gs
    let output:=listAppendProgram gate.value.word tail.value.word
    let programs:=listAppendProgram gate.value.programs tail.value.programs
    ⟨⟨output.value,programs.value⟩,.joined gate.trace tail.trace output.trace programs.trace⟩


theorem materializeGate_value {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (g : GateCode wires) : (materializeGate synth g).value=compileAssembledGate synth g := by
  cases g <;> simp only [materializeGate,compileAssembledGate,wireLabelProgram_word]


theorem materializeWord_value {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (xs : WordCode wires) : (materializeWord synth xs).value=compileAssembledWord synth xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [materializeWord,compileAssembledWord,listAppendProgram_value,materializeGate_value,ih]


theorem materializeGate_headActions {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (g : GateCode wires) (B : ℕ)
    (h : ∀ wire u,g=GateCode.single wire u → (synth u).cached.program.program.word.length≤B) :
    (materializeGate synth g).trace.actions+4*(materializeGate synth g).value.word.length+1+
      (4*(materializeGate synth g).value.programs.length+1)≤12*(B+2) := by
  cases g with
  | single wire u =>
    have hu:=h wire u rfl
    simp only [materializeGate,OuterLabelTrace.actions,wireLabelProgram_actions,wireLabelProgram_word,
      wireLabels,List.length_map,List.length_cons,List.length_nil]
    omega
  | cnot c t hct =>
    simp only [materializeGate,OuterLabelTrace.actions,List.length_cons,List.length_nil]
    omega


theorem materializeWord_actions {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → (synth u).cached.program.program.word.length≤B) :
    (materializeWord synth xs).trace.actions≤xs.length*(12*(B+2))+1 := by
  induction xs with
  | nil => simp [materializeWord,OuterLabelTrace.actions]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    have hg:=materializeGate_headActions synth g B (by
      intro wire u heq
      exact h wire u (by simp [heq]))
    simp only [materializeWord,OuterLabelTrace.actions,listAppendProgram_actions,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end EffectiveEncoding
