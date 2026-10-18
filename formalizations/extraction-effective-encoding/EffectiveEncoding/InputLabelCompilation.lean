import EffectiveEncoding.RetainedInputTarget

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure InputCompiledLabelRun (m wires L q : ℕ) where
  word : List (LabelGate m wires)
  programs : List (RetainedInputTargetResult m L q)


def compileInputGate {m wires L q : ℕ} (synth : SingleCode → RetainedInputTargetResult m L q) :
    GateCode wires → InputCompiledLabelRun m wires L q
  | .single wire u =>
    let program:=synth u
    ⟨wireLabels wire program.cached.program.word,[program]⟩
  | .cnot c t h => ⟨[.cnot c t h],[]⟩

/-- One actual retained provider/input-reference execution per single. -/
def compileInputWord {m wires L q : ℕ} (synth : SingleCode → RetainedInputTargetResult m L q) :
    WordCode wires → InputCompiledLabelRun m wires L q
  | [] => ⟨[],[]⟩
  | g::gs =>
    let gate:=compileInputGate synth g
    let tail:=compileInputWord synth gs
    ⟨gate.word++tail.word,gate.programs++tail.programs⟩


theorem compileInputWord_word {m wires L q : ℕ} (synth : SingleCode → RetainedInputTargetResult m L q)
    (xs : WordCode wires) :
    (compileInputWord synth xs).word=compileLabelWord (fun u => (synth u).cached.program.word) xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp only [compileInputWord,compileInputGate,compileLabelWord,
      List.flatMap_cons,compileLabels,ih]

/-- A list projection helper, used below only for concrete retained traces.
This traversal and its counter arithmetic are not charged by its result. -/
def InputCompiledLabelRun.sumCharge {m wires L q : ℕ} (f : RetainedInputTargetResult m L q → ℕ)
    (r : InputCompiledLabelRun m wires L q) : ℕ := (r.programs.map f).sum


theorem compileInputWord_sumCharge {m wires L q : ℕ}
    (synth : SingleCode → RetainedInputTargetResult m L q) (f : RetainedInputTargetResult m L q → ℕ)
    (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → f (synth u)≤B) :
    (compileInputWord synth xs).sumCharge f≤xs.length*B := by
  induction xs with
  | nil => simp [compileInputWord,InputCompiledLabelRun.sumCharge]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    cases g with
    | single wire u =>
      have hg:=h wire u (by simp)
      simp only [compileInputWord,compileInputGate,InputCompiledLabelRun.sumCharge,List.map_append,
        List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_cons] at *
      nlinarith
    | cnot c t hct =>
      simp only [compileInputWord,compileInputGate,InputCompiledLabelRun.sumCharge,
        List.nil_append,List.length_cons] at *
      nlinarith


def InputCompiledLabelRun.preparationActions {m wires L q : ℕ} (r : InputCompiledLabelRun m wires L q) : ℕ :=
  r.sumCharge (fun x => x.prepared.preparationActions)
def InputCompiledLabelRun.providerActions {m wires L q : ℕ} (r : InputCompiledLabelRun m wires L q) : ℕ :=
  r.sumCharge RetainedInputTargetResult.providerActions
def InputCompiledLabelRun.onlineActions {m wires L q : ℕ} (r : InputCompiledLabelRun m wires L q) : ℕ :=
  r.sumCharge (fun x => x.cached.program.onlineActions)

end EffectiveEncoding
