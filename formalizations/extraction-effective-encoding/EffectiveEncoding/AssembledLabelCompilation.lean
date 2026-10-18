import EffectiveEncoding.RetainedAssembledTarget

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure AssembledCompiledLabelRun (m wires L q : ℕ) where
  word : List (LabelGate m wires)
  programs : List (RetainedAssembledTargetResult m L q)


def AssembledCompiledLabelRun.erase {m wires L q : ℕ}
    (r : AssembledCompiledLabelRun m wires L q) : InputCompiledLabelRun m wires L q :=
  ⟨r.word,r.programs.map RetainedAssembledTargetResult.erase⟩


def compileAssembledGate {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q) :
    GateCode wires → AssembledCompiledLabelRun m wires L q
  | .single wire u =>
    let program:=synth u
    ⟨wireLabels wire program.cached.program.program.word,[program]⟩
  | .cnot c t h => ⟨[.cnot c t h],[]⟩

/-- Every assembled target/numerical/read run is executed once and stored. -/
def compileAssembledWord {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q) :
    WordCode wires → AssembledCompiledLabelRun m wires L q
  | [] => ⟨[],[]⟩
  | g::gs =>
    let gate:=compileAssembledGate synth g
    let tail:=compileAssembledWord synth gs
    ⟨gate.word++tail.word,gate.programs++tail.programs⟩


theorem compileAssembledGate_erase {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (g : GateCode wires) :
    (compileAssembledGate synth g).erase=compileInputGate (fun u => (synth u).erase) g := by
  cases g <;> rfl


theorem compileAssembledWord_erase {m wires L q : ℕ} (synth : SingleCode → RetainedAssembledTargetResult m L q)
    (xs : WordCode wires) :
    (compileAssembledWord synth xs).erase=compileInputWord (fun u => (synth u).erase) xs := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    have hg:=compileAssembledGate_erase synth g
    cases hg' : compileAssembledGate synth g with
    | mk word programs =>
      cases ht' : compileAssembledWord synth gs with
      | mk tail tailPrograms =>
        simp only [hg',ht',AssembledCompiledLabelRun.erase] at hg ih
        simp only [compileAssembledWord,compileInputWord,hg',ht',←hg,←ih,
          AssembledCompiledLabelRun.erase,List.map_append]

/-- Projection helper only for fields of actual execution records. -/
def AssembledCompiledLabelRun.sumTrace {m wires L q : ℕ}
    (f : RetainedAssembledTargetResult m L q → ℕ) (r : AssembledCompiledLabelRun m wires L q) : ℕ :=
  (r.programs.map f).sum


theorem compileAssembledWord_sumTrace {m wires L q : ℕ}
    (synth : SingleCode → RetainedAssembledTargetResult m L q) (f : RetainedAssembledTargetResult m L q → ℕ)
    (xs : WordCode wires) (B : ℕ)
    (h : ∀ wire u,GateCode.single wire u∈xs → f (synth u)≤B) :
    (compileAssembledWord synth xs).sumTrace f≤xs.length*B := by
  induction xs with
  | nil => simp [compileAssembledWord,AssembledCompiledLabelRun.sumTrace]
  | cons g gs ih =>
    have ht:=ih (fun wire u hu => h wire u (by simp [hu]))
    cases g with
    | single wire u =>
      have hg:=h wire u (by simp)
      simp only [compileAssembledWord,compileAssembledGate,AssembledCompiledLabelRun.sumTrace,List.map_append,
        List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_cons] at *
      nlinarith
    | cnot c t hct =>
      simp only [compileAssembledWord,compileAssembledGate,AssembledCompiledLabelRun.sumTrace,
        List.nil_append,List.length_cons] at *
      nlinarith


def AssembledCompiledLabelRun.assemblyActions {m wires L q : ℕ} (r : AssembledCompiledLabelRun m wires L q) : ℕ :=
  r.sumTrace RetainedAssembledTargetResult.assemblyActions

def AssembledCompiledLabelRun.inverseCalls {m wires L q : ℕ} (r : AssembledCompiledLabelRun m wires L q) : ℕ :=
  r.sumTrace RetainedAssembledTargetResult.inverseCalls

theorem AssembledCompiledLabelRun.inverseCalls_le_assemblyActions {m wires L q : ℕ}
    (r : AssembledCompiledLabelRun m wires L q) : r.inverseCalls≤r.assemblyActions := by
  rcases r with ⟨word,programs⟩
  change (programs.map RetainedAssembledTargetResult.inverseCalls).sum≤
    (programs.map RetainedAssembledTargetResult.assemblyActions).sum
  induction programs with
  | nil => rfl
  | cons r rs ih =>
    exact Nat.add_le_add (InputListAssemblyTrace.inverseCalls_le_actions r.cached.program.trace) ih

end EffectiveEncoding
