import EffectiveEncoding.BooleanRankGenerationPrograms
import EffectiveEncoding.BinaryDescriptorGeneration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def scannedNativeBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    List (NativeOccupation (k+1)) → ScannedGeneratedRun (2+codeWires k)
  | [] => ⟨⟨⟨[],fun _ => 0⟩,[]⟩,[]⟩
  | x::xs =>
    let branch:=scannedNativeBranchRun plans x
    let tail:=scannedNativeBranchTableRun plans xs
    ⟨⟨⟨branch.result.result.word++tail.result.result.word,
      fun i => branch.result.result.work i+tail.result.result.work i⟩,
      branch.result.programs++tail.result.programs⟩,branch.scans++tail.scans⟩


theorem scannedNativeBranchTableRun_result {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (scannedNativeBranchTableRun plans xs).result=binaryNativeBranchTableRun plans xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scannedNativeBranchTableRun,binaryNativeBranchTableRun,scannedNativeBranchRun_result,ih]


theorem scannedNativeBranchTableRun_scanActions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (scannedNativeBranchTableRun plans xs).scanActions≤1200*(k+3)^5*xs.length := by
  induction xs with
  | nil => exact le_refl 0
  | cons x xs ih =>
    change booleanRankRecordsActions ((scannedNativeBranchRun plans x).scans++_)≤_
    rw [booleanRankRecordsActions_append]
    exact (Nat.add_le_add (scannedNativeBranchRun_scanActions plans x) ih).trans_eq
      (by simp only [List.length_cons];ring)

/-- All rank choices now execute Boolean scans. The actual native table and
shared Pauli context are still each built once for this occupation stage. -/
def scannedNativeOccupationRun (k : ℕ) : ScannedGeneratedRun (2+codeWires k) :=
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let xs:=nativeOccupationTable (k+1)
  let branches:=scannedNativeBranchTableRun plans xs
  let aligned:=scannedAlignmentRun plans scannedNativePivotEndpoint scannedNativeNextEndpoint xs []
  ⟨⟨⟨branches.result.result.word++aligned.result.result.result.word,
    fun i => branches.result.result.work i+aligned.result.result.work i⟩,
    branches.result.programs++aligned.result.programs⟩,branches.scans++aligned.scans⟩


theorem scannedNativeOccupationRun_result (k : ℕ) :
    (scannedNativeOccupationRun k).result=binaryNativeOccupationRun k := by
  have he : (fun x : NativeOccupation (k+1) => (scannedNativePivotEndpoint x).binary)=binaryNativePivotEndpoint :=
    funext scannedNativePivotEndpoint_binary
  have hf : (fun x : NativeOccupation (k+1) => (scannedNativeNextEndpoint x).binary)=binaryNativeNextEndpoint :=
    funext scannedNativeNextEndpoint_binary
  simp only [scannedNativeOccupationRun,binaryNativeOccupationRun,scannedNativeBranchTableRun_result,
    scannedAlignmentRun_result,he,hf]


theorem scannedNativeOccupationRun_scanActions (k : ℕ) :
    (scannedNativeOccupationRun k).scanActions≤1800*(k+3)^8 := by
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let xs:=nativeOccupationTable (k+1)
  have hb:=scannedNativeBranchTableRun_scanActions plans xs
  have ha:=scannedAlignmentRun_scanActions plans scannedNativePivotEndpoint scannedNativeNextEndpoint xs []
    (300*(k+3)^5) scannedNativePivotEndpoint_scanActions scannedNativeNextEndpoint_scanActions
  have hl : xs.length≤(k+3)^3 := by
    have h:=enumeration_candidate_bound (k+1)
    rw [←nativeOccupationTable_values,List.length_map] at h
    exact h.trans (Nat.pow_le_pow_left (by omega) 3)
  change booleanRankRecordsActions ((scannedNativeBranchTableRun plans xs).scans++
    (scannedAlignmentRun plans scannedNativePivotEndpoint scannedNativeNextEndpoint xs []).scans)≤_
  rw [booleanRankRecordsActions_append]
  calc
    _≤1200*(k+3)^5*xs.length+2*(300*(k+3)^5)*xs.length := Nat.add_le_add hb ha
    _=1800*(k+3)^5*xs.length := by ring
    _≤1800*(k+3)^5*(k+3)^3 := Nat.mul_le_mul_left _ hl
    _=1800*(k+3)^8 := by ring


def scannedNativeStageRun (k : ℕ) : ScannedGeneratedRun (originalWireCount (k+1)) :=
  let active:=scannedNativeOccupationRun k
  ⟨⟨⟨prefixCode (active_available k) active.result.result.word,active.result.result.work⟩,active.result.programs⟩,
    active.scans⟩


theorem scannedNativeStageRun_result (k : ℕ) :
    (scannedNativeStageRun k).result=binaryNativeStageRun k := by
  simp only [scannedNativeStageRun,binaryNativeStageRun,scannedNativeOccupationRun_result]


def scannedNativeCompressionRun : (k : ℕ) → ScannedGeneratedRun (originalWireCount k)
  | 0 => ⟨⟨⟨[],fun _ => 0⟩,[]⟩,[]⟩
  | k+1 =>
    let previous:=scannedNativeCompressionRun k
    let stage:=scannedNativeStageRun k
    ⟨⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.result.result.word)++stage.result.result.word,
      fun i => previous.result.result.work i+stage.result.result.work i⟩,
      previous.result.programs++stage.result.programs⟩,previous.scans++stage.scans⟩


theorem scannedNativeCompressionRun_result (k : ℕ) :
    (scannedNativeCompressionRun k).result=binaryNativeCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scannedNativeCompressionRun,binaryNativeCompressionRun,scannedNativeStageRun_result,ih]


theorem scannedNativeCompressionRun_scanActions (k : ℕ) :
    (scannedNativeCompressionRun k).scanActions≤1800*k*(k+3)^8 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs:=scannedNativeOccupationRun_scanActions k
    have hp:=Nat.pow_le_pow_left (show k+3≤k+1+3 by omega) 8
    have hi':=ih.trans (Nat.mul_le_mul_left (1800*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 1800 hp)
    change booleanRankRecordsActions ((scannedNativeCompressionRun k).scans++(scannedNativeStageRun k).scans)≤_
    rw [booleanRankRecordsActions_append]
    exact (Nat.add_le_add hi' hs').trans_eq (by ring)


def scannedNativeDescriptorRun (k : ℕ) : ScannedGeneratedRun (originalWireCount k) :=
  let compression:=scannedNativeCompressionRun k
  ⟨⟨⟨compression.result.result.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.result.result.work⟩,
    compression.result.programs⟩,compression.scans⟩

/-- Entire previous generator record, including actual rank-digit traces.
The new scan traces are additional records of its actual Boolean decisions. -/
theorem scannedNativeDescriptorRun_result (k : ℕ) :
    (scannedNativeDescriptorRun k).result=binaryNativeDescriptorRun k := by
  simp only [scannedNativeDescriptorRun,binaryNativeDescriptorRun,scannedNativeCompressionRun_result]


theorem scannedNativeDescriptorRun_scanActions (k : ℕ) :
    (scannedNativeDescriptorRun k).scanActions≤1800*k*(k+3)^8 :=
  scannedNativeCompressionRun_scanActions k

end EffectiveEncoding
