import EffectiveEncoding.PreparedRankedPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def preparedNativeBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    List (NativeOccupation (k+1)) → RankedBranchRun (2+codeWires k)
  | [] => ⟨[],fun _ => 0⟩
  | x::xs =>
    let branch:=preparedNativeBranchRun plans x
    let tail:=preparedNativeBranchTableRun plans xs
    ⟨branch.word++tail.word,fun i => branch.work i+tail.work i⟩


theorem preparedNativeBranchTableRun_eq {k : ℕ} (xs : List (NativeOccupation (k+1))) :
    preparedNativeBranchTableRun (preparedMaskTable (by omega)) xs=nativeBranchTableRun xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [preparedNativeBranchTableRun,nativeBranchTableRun,preparedNativeBranchRun_eq,ih]

/-- One actual mask context and one native occupation table are built per stage.
The same context is shared by every branch and every packed alignment swap. -/
def preparedNativeOccupationRun (k : ℕ) : RankedBranchRun (2+codeWires k) :=
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let occupationsHere:=nativeOccupationTable (k+1)
  let branches:=preparedNativeBranchTableRun plans occupationsHere
  let aligned:=preparedRankedAlignmentRun plans nativePivotEndpoint nativeNextEndpoint occupationsHere []
  ⟨branches.word++aligned.result.word,fun i => branches.work i+aligned.work i⟩


theorem preparedNativeOccupationRun_eq (k : ℕ) :
    preparedNativeOccupationRun k=nativeOccupationRun k := by
  simp only [preparedNativeOccupationRun,nativeOccupationRun,nativeAlignmentRun,
    preparedNativeBranchTableRun_eq,preparedRankedAlignmentRun_eq]


def preparedNativeStageRun (k : ℕ) : RankedBranchRun (originalWireCount (k+1)) :=
  let active:=preparedNativeOccupationRun k
  ⟨prefixCode (active_available k) active.word,active.work⟩


theorem preparedNativeStageRun_eq (k : ℕ) : preparedNativeStageRun k=nativeStageRun k := by
  simp only [preparedNativeStageRun,nativeStageRun,preparedNativeOccupationRun_eq]


def preparedNativeCompressionRun : (k : ℕ) → RankedBranchRun (originalWireCount k)
  | 0 => ⟨[],fun _ => 0⟩
  | k+1 =>
    let previous:=preparedNativeCompressionRun k
    let stage:=preparedNativeStageRun k
    ⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      fun i => previous.work i+stage.work i⟩


theorem preparedNativeCompressionRun_eq (k : ℕ) :
    preparedNativeCompressionRun k=nativeCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [preparedNativeCompressionRun,nativeCompressionRun,preparedNativeStageRun_eq,ih]


def preparedNativeDescriptorRun (k : ℕ) : RankedBranchRun (originalWireCount k) :=
  let compression:=preparedNativeCompressionRun k
  ⟨compression.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.work⟩


theorem preparedNativeDescriptorRun_eq (k : ℕ) :
    preparedNativeDescriptorRun k=nativeDescriptorRun k := by
  simp only [preparedNativeDescriptorRun,nativeDescriptorRun,preparedNativeCompressionRun_eq]


theorem nativeActiveWires_eq (k : ℕ) : 2+codeWires k=activeWires k := by
  unfold codeWires activeWires
  omega

/-- Storage cells of the actually shared stage context, not a constructor or
bit-time fee. The context contains finite metadata at active logarithmic width. -/
theorem activePreparedMaskPayload (k : ℕ) :
    preparedMaskTablePayload (preparedMaskTable (by omega : 0<2+codeWires k))≤352*(k+3)^4 := by
  have hd : 2^(2+codeWires k)≤16*(k+3)^3 := by
    rw [nativeActiveWires_eq]
    exact activeDimension_polynomial k
  have hw:=activeWires_log_bound k
  rw [←nativeActiveWires_eq] at hw
  have hc : Nat.clog 2 (k+3)≤k+3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hf : 3*(2+codeWires k)+2≤22*(k+3) := by omega
  calc
    _≤2^(2+codeWires k)*(3*(2+codeWires k)+2) := preparedMaskTablePayload_bound _
    _≤16*(k+3)^3*(22*(k+3)) := Nat.mul_le_mul hd hf
    _=352*(k+3)^4 := by ring

end EffectiveEncoding
