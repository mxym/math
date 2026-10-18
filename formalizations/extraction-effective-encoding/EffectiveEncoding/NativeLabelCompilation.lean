import EffectiveEncoding.NativeTargetCached

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure NativeCompiledLabelRun (m wires L q : ℕ) where
  word : List (LabelGate m wires)
  programs : List (NativeTargetResult m L q)


def compileNativeGate {m wires L q : ℕ} (synth : SingleCode → NativeTargetResult m L q) :
    GateCode wires → NativeCompiledLabelRun m wires L q
  | .single wire u =>
    let program:=synth u
    ⟨wireLabels wire program.cached.program.word,[program]⟩
  | .cnot c t h => ⟨[.cnot c t h],[]⟩

/-- Each actual single target/provider/cache/synthesis program is executed once
and retained. Output labels and later resource projections read these records. -/
def compileNativeWord {m wires L q : ℕ} (synth : SingleCode → NativeTargetResult m L q) :
    WordCode wires → NativeCompiledLabelRun m wires L q
  | [] => ⟨[],[]⟩
  | g::gs =>
    let gate:=compileNativeGate synth g
    let tail:=compileNativeWord synth gs
    ⟨gate.word++tail.word,gate.programs++tail.programs⟩


theorem compileNativeWord_word {m wires L q : ℕ} (synth : SingleCode → NativeTargetResult m L q)
    (xs : WordCode wires) :
    (compileNativeWord synth xs).word=compileLabelWord (fun u => (synth u).cached.program.word) xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [compileNativeWord,compileNativeGate,compileLabelWord,
      List.flatMap_cons,compileLabels,ih]


theorem compileNativeWord_programs_length {m wires L q : ℕ} (synth : SingleCode → NativeTargetResult m L q)
    (xs : WordCode wires) : (compileNativeWord synth xs).programs.length≤xs.length := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons g gs ih => cases g <;> simp only [compileNativeWord,compileNativeGate,List.length_append,
      List.length_singleton,List.length_nil,List.length_cons,Nat.zero_add] <;> omega

/-- A projection of actual stored literal-preparation traces. It does not
re-run any encoding/provider, nor charge the projection's own sum/traversal. -/
def NativeCompiledLabelRun.preparationActions {m wires L q : ℕ}
    (run : NativeCompiledLabelRun m wires L q) : ℕ :=
  (run.programs.map (fun r => r.prepared.preparationActions)).sum


theorem compileNativeWord_preparationActions {m wires L q : ℕ}
    (synth : SingleCode → NativeTargetResult m L q) (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → (synth u).prepared.preparationActions≤B) :
    (compileNativeWord synth xs).preparationActions≤xs.length*B := by
  induction xs with
  | nil => simp [compileNativeWord,NativeCompiledLabelRun.preparationActions]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    cases g with
    | single wire u =>
      have hg:=h wire u (by simp)
      simp only [compileNativeWord,compileNativeGate,NativeCompiledLabelRun.preparationActions,
        List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
        Nat.add_zero,List.length_cons] at *
      nlinarith
    | cnot c t hct =>
      simp only [compileNativeWord,compileNativeGate,NativeCompiledLabelRun.preparationActions,
        List.nil_append,List.length_cons] at *
      nlinarith

end EffectiveEncoding
