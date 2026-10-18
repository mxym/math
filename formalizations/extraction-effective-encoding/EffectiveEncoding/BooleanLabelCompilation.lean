import EffectiveEncoding.BooleanDescriptorBudgets

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Two distinct returned annotations: online Boolean/list numeric actions,
and target-provider root-only actions. They are never added to each other. -/
abbrev BooleanCompilationWork := Fin 2 → ℕ

structure BooleanLabelRun (m wires : ℕ) where
  word : List (LabelGate m wires)
  work : BooleanCompilationWork


def booleanCompileGate {m w : ℕ} (synth : SingleCode → BooleanProviderResult m) :
    GateCode w → BooleanLabelRun m w
  | .single i u =>
    let program:=synth u
    ⟨wireLabels i program.online.result.word,![program.online.booleanActions,program.providerRootCharge]⟩
  | .cnot c t h => ⟨[.cnot c t h],fun _ => 0⟩

/-- Compile each gate once, retaining its returned word and both annotations.
The sums read stored program records; they do not re-run the numeric synthesis.
Output concatenation and annotation maintenance are not charged here. -/
def booleanCompileWord {m w : ℕ} (synth : SingleCode → BooleanProviderResult m) :
    WordCode w → BooleanLabelRun m w
  | [] => ⟨[],fun _ => 0⟩
  | g::gs =>
    let gate:=booleanCompileGate synth g
    let tail:=booleanCompileWord synth gs
    ⟨gate.word++tail.word,fun i => gate.work i+tail.work i⟩


theorem booleanCompileWord_word {m w : ℕ} (synth : SingleCode → BooleanProviderResult m) (xs : WordCode w) :
    (booleanCompileWord synth xs).word=compileLabelWord (fun u => (synth u).online.result.word) xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [booleanCompileWord,booleanCompileGate,compileLabelWord,
      List.flatMap_cons,compileLabels,ih]


theorem booleanCompileWord_work {m w : ℕ} (synth : SingleCode → BooleanProviderResult m)
    (xs : WordCode w) (i : Fin 2) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs →
      (![ (synth u).online.booleanActions,(synth u).providerRootCharge] : BooleanCompilationWork) i≤B) :
    (booleanCompileWord synth xs).work i≤xs.length*B := by
  induction xs with
  | nil => simp [booleanCompileWord]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    have hg : (booleanCompileGate synth g).work i≤B := by
      cases g with
      | single wire u => exact h wire u (by simp)
      | cnot c t hct => exact Nat.zero_le _
    change (booleanCompileGate synth g).work i+(booleanCompileWord synth gs).work i≤_
    calc
      _≤B+gs.length*B := Nat.add_le_add hg ht
      _=(g::gs).length*B := by simp only [List.length_cons];ring

end EffectiveEncoding
