import EffectiveEncoding.RetainedNativeProvider

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure ProviderCompiledLabelRun (m wires L q : ℕ) where
  word : List (LabelGate m wires)
  programs : List (RetainedNativeTargetResult m L q)


def ProviderCompiledLabelRun.erase {m wires L q : ℕ}
    (r : ProviderCompiledLabelRun m wires L q) : NativeCompiledLabelRun m wires L q :=
  ⟨r.word,r.programs.map RetainedNativeTargetResult.erase⟩


def compileProviderGate {m wires L q : ℕ} (synth : SingleCode → RetainedNativeTargetResult m L q) :
    GateCode wires → ProviderCompiledLabelRun m wires L q
  | .single wire u =>
    let program:=synth u
    ⟨wireLabels wire program.cached.program.word,[program]⟩
  | .cnot c t h => ⟨[.cnot c t h],[]⟩

/-- Each single execution is stored once. Output labels, provider traces and
online numeric traces all project from those same execution records. -/
def compileProviderWord {m wires L q : ℕ} (synth : SingleCode → RetainedNativeTargetResult m L q) :
    WordCode wires → ProviderCompiledLabelRun m wires L q
  | [] => ⟨[],[]⟩
  | g::gs =>
    let gate:=compileProviderGate synth g
    let tail:=compileProviderWord synth gs
    ⟨gate.word++tail.word,gate.programs++tail.programs⟩


theorem compileProviderGate_erase {m wires L q : ℕ} (synth : SingleCode → RetainedNativeTargetResult m L q)
    (g : GateCode wires) :
    (compileProviderGate synth g).erase=compileNativeGate (fun u => (synth u).erase) g := by
  cases g <;> rfl


theorem compileProviderWord_erase {m wires L q : ℕ} (synth : SingleCode → RetainedNativeTargetResult m L q)
    (xs : WordCode wires) :
    (compileProviderWord synth xs).erase=compileNativeWord (fun u => (synth u).erase) xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    have hg:=compileProviderGate_erase synth g
    cases hg' : compileProviderGate synth g with
    | mk word programs =>
      cases ht' : compileProviderWord synth gs with
      | mk tail tailPrograms =>
        simp only [hg',ht',ProviderCompiledLabelRun.erase] at hg ih
        simp only [compileProviderWord,compileNativeWord,hg',ht',←hg,←ih,
          ProviderCompiledLabelRun.erase,List.map_append]


def ProviderCompiledLabelRun.providerActions {m wires L q : ℕ}
    (r : ProviderCompiledLabelRun m wires L q) : ℕ :=
  (r.programs.map RetainedNativeTargetResult.providerActions).sum


theorem compileProviderWord_providerActions {m wires L q : ℕ}
    (synth : SingleCode → RetainedNativeTargetResult m L q) (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → (synth u).providerActions≤B) :
    (compileProviderWord synth xs).providerActions≤xs.length*B := by
  induction xs with
  | nil => simp [compileProviderWord,ProviderCompiledLabelRun.providerActions]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    cases g with
    | single wire u =>
      have hg:=h wire u (by simp)
      simp only [compileProviderWord,compileProviderGate,ProviderCompiledLabelRun.providerActions,
        List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
        Nat.add_zero,List.length_cons] at *
      nlinarith
    | cnot c t hct =>
      simp only [compileProviderWord,compileProviderGate,ProviderCompiledLabelRun.providerActions,
        List.nil_append,List.length_cons] at *
      nlinarith

end EffectiveEncoding
