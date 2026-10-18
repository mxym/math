import EffectiveEncoding.NativeRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def nativeBranchTableRun {k : ℕ} : List (NativeOccupation (k+1)) → RankedBranchRun (2+codeWires k)
  | [] => ⟨[],fun _ => 0⟩
  | x::xs =>
    let branch:=nativeBranchRun x
    let tail:=nativeBranchTableRun xs
    ⟨branch.word++tail.word,fun i => branch.work i+tail.work i⟩


theorem nativeBranchTableRun_eq {k : ℕ} (xs : List (NativeOccupation (k+1))) :
    nativeBranchTableRun xs=rankedBranchTableRun (xs.map nativeOccupationValue) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [nativeBranchTableRun,rankedBranchTableRun,List.map_cons,nativeBranchRun_eq,ih]


def nativeAlignmentRun {k : ℕ} (xs : List (NativeOccupation (k+1))) : RankedAlignmentRun (2+codeWires k) :=
  rankedAlignmentRun (by omega) nativePivotEndpoint nativeNextEndpoint xs []


theorem nativeAlignmentRun_eq {k : ℕ} (xs : List (NativeOccupation (k+1))) :
    nativeAlignmentRun xs=rankedAlignmentRun (by omega) encodedPivotEndpoint encodedNextEndpoint
      (xs.map nativeOccupationValue) [] :=
  rankedAlignmentRun_map_eq _ _ _ _ _ _ nativePivotEndpoint_eq nativeNextEndpoint_eq _ _

/-- The actual stage table stores only native triples and erased proofs.
No semantic occupation value is computed by branch, alignment or ranking. -/
def nativeOccupationRun (k : ℕ) : RankedBranchRun (2+codeWires k) :=
  let occupationsHere:=nativeOccupationTable (k+1)
  let branches:=nativeBranchTableRun occupationsHere
  let aligned:=nativeAlignmentRun occupationsHere
  ⟨branches.word++aligned.result.word,fun i => branches.work i+aligned.work i⟩


theorem nativeOccupationRun_eq (k : ℕ) : nativeOccupationRun k=rankedOccupationRun k := by
  simp only [nativeOccupationRun,rankedOccupationRun,nativeBranchTableRun_eq,
    nativeAlignmentRun_eq,nativeOccupationTable_values,literalOccupationTable_value,builtOccupations_eq]


def nativeStageRun (k : ℕ) : RankedBranchRun (originalWireCount (k+1)) :=
  let active:=nativeOccupationRun k
  ⟨prefixCode (active_available k) active.word,active.work⟩


theorem nativeStageRun_eq (k : ℕ) : nativeStageRun k=rankedStageRun k := by
  simp only [nativeStageRun,rankedStageRun,nativeOccupationRun_eq]


def nativeCompressionRun : (k : ℕ) → RankedBranchRun (originalWireCount k)
  | 0 => ⟨[],fun _ => 0⟩
  | k+1 =>
    let previous:=nativeCompressionRun k
    let stage:=nativeStageRun k
    ⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      fun i => previous.work i+stage.work i⟩


theorem nativeCompressionRun_eq (k : ℕ) : nativeCompressionRun k=rankedCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [nativeCompressionRun,rankedCompressionRun,nativeStageRun_eq,ih]


def nativeDescriptorRun (k : ℕ) : RankedBranchRun (originalWireCount k) :=
  let compression:=nativeCompressionRun k
  ⟨compression.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.work⟩


theorem nativeDescriptorRun_eq (k : ℕ) : nativeDescriptorRun k=rankedDescriptorRun k := by
  simp only [nativeDescriptorRun,rankedDescriptorRun,nativeCompressionRun_eq]


theorem nativeDescriptorRun_work (k : ℕ) (i : Fin 3) :
    (nativeDescriptorRun k).work i≤6*rankWorkConstant i*k*(k+2)^6 := by
  rw [nativeDescriptorRun_eq]
  exact rankedDescriptorRun_work k i

end EffectiveEncoding
