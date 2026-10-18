import EffectiveEncoding.NativeMergeInputs

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

inductive NativeAtomInput where
  | pi
  | trivial
  | merge : NativeMergeInputResult → NativeAtomInput

/-- Prepare native dynamic literal payloads once, independently of the later
precision. The degenerate test uses native Nat control, separately uncharged. -/
def prepareNativeAtomInput : AngleAtom → NativeAtomInput
  | .pi => .pi
  | .merge A B j => if h : j=0 ∨ A+B=0 then .trivial else
      .merge (nativeMergeInputProgram A B (by omega))


def NativeAtomInput.preparationActions : NativeAtomInput → ℕ
  | .pi | .trivial => 0
  | .merge r => r.incrementTrimActions

structure NativeAngleInput where
  atom : NativeAtomInput
  negative : Bool
  halvings : ℕ


def prepareNativeAngleInput (a : AngleCode) : NativeAngleInput :=
  ⟨prepareNativeAtomInput a.atom,a.negative,a.halvings⟩

inductive NativeSingleInput where
  | hadamard
  | yBasis
  | phase : NativeAngleInput → NativeAngleInput → NativeSingleInput
  | inverse : NativeSingleInput → NativeSingleInput


def prepareNativeSingleInput : SingleCode → NativeSingleInput
  | .hadamard => .hadamard
  | .yBasis => .yBasis
  | .phase a b => .phase (prepareNativeAngleInput a) (prepareNativeAngleInput b)
  | .inverse u => .inverse (prepareNativeSingleInput u)


def NativeSingleInput.preparationActions : NativeSingleInput → ℕ
  | .hadamard | .yBasis => 0
  | .phase a b => a.atom.preparationActions+b.atom.preparationActions
  | .inverse u => u.preparationActions


theorem prepareNativeAngleInput_actions {M H : ℕ} (a : AngleCode) (h : a.Fits M H) :
    (prepareNativeAngleInput a).atom.preparationActions≤100*(M+2)^2 := by
  cases ha : a.atom with
  | pi => simp [prepareNativeAngleInput,prepareNativeAtomInput,ha,NativeAtomInput.preparationActions]
  | merge A B j =>
    have hm : A+B≤M := by
      have hh:=h.1
      rw [ha] at hh
      exact hh.1
    by_cases hz : j=0 ∨ A+B=0
    · simp only [prepareNativeAngleInput,prepareNativeAtomInput,ha,dite_eq_left hz,NativeAtomInput.preparationActions]
      exact Nat.zero_le _
    · simp only [prepareNativeAngleInput,prepareNativeAtomInput,ha,dite_eq_right hz,
        NativeAtomInput.preparationActions]
      exact nativeMergeInputProgram_actions A B M (by omega) hm


theorem prepareNativeSingleInput_actions {M H : ℕ} (u : SingleCode) (h : u.Fits M H) :
    (prepareNativeSingleInput u).preparationActions≤200*(M+2)^2 := by
  induction u with
  | hadamard => simp [prepareNativeSingleInput,NativeSingleInput.preparationActions]
  | yBasis => simp [prepareNativeSingleInput,NativeSingleInput.preparationActions]
  | phase a b =>
    have ha:=prepareNativeAngleInput_actions a h.1
    have hb:=prepareNativeAngleInput_actions b h.2
    simp only [prepareNativeSingleInput,NativeSingleInput.preparationActions]
    omega
  | inverse u ih => exact ih h


theorem extractionCode_nativeInput_preparationActions {k : ℕ}
    {wire : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single wire u∈extractionCode k) :
    (prepareNativeSingleInput u).preparationActions≤200*(4*k+2)^2 :=
  prepareNativeSingleInput_actions u (extractionCode_fits k _ hu).1


theorem preparedNativeCode_input_preparationActions {k : ℕ}
    {wire : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) :
    (prepareNativeSingleInput u).preparationActions≤200*(4*k+2)^2 := by
  rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord] at hu
  exact extractionCode_nativeInput_preparationActions hu

end EffectiveEncoding
