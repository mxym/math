import EffectiveEncoding.BinaryRankAlignmentPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Native occupation generation with all rank-bit executions retained.
The actual mask plan and native occupation table are each prepared once. -/
def binaryNativeOccupationRun (k : ℕ) : BinaryGeneratedRun (2+codeWires k) :=
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let xs:=nativeOccupationTable (k+1)
  let branches:=binaryNativeBranchTableRun plans xs
  let aligned:=binaryAlignmentRun plans binaryNativePivotEndpoint binaryNativeNextEndpoint xs []
  ⟨⟨branches.result.word++aligned.result.result.word,
    fun i => branches.result.work i+aligned.result.work i⟩,branches.programs++aligned.programs⟩


theorem binaryNativeOccupationRun_result (k : ℕ) :
    (binaryNativeOccupationRun k).result=preparedNativeOccupationRun k := by
  have he : (fun x : NativeOccupation (k+1) => (binaryNativePivotEndpoint x).endpoint)=nativePivotEndpoint :=
    funext binaryNativePivotEndpoint_endpoint
  have hf : (fun x : NativeOccupation (k+1) => (binaryNativeNextEndpoint x).endpoint)=nativeNextEndpoint :=
    funext binaryNativeNextEndpoint_endpoint
  simp only [binaryNativeOccupationRun,preparedNativeOccupationRun,binaryNativeBranchTableRun_result,
    binaryAlignmentRun_result,he,hf]


theorem binaryNativeOccupationRun_encodingActions (k : ℕ) :
    (binaryNativeOccupationRun k).encodingActions≤306*(k+4)^9 := by
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let xs:=nativeOccupationTable (k+1)
  have hb:=binaryNativeBranchTableRun_encodingActions plans xs
  have ha:=binaryAlignmentRun_encodingActions plans binaryNativePivotEndpoint binaryNativeNextEndpoint xs []
    (51*(k+4)^6) binaryNativePivotEndpoint_encodingActions binaryNativeNextEndpoint_encodingActions
  have hl : xs.length≤(k+4)^3 := by
    have h:=enumeration_candidate_bound (k+1)
    rw [←nativeOccupationTable_values,List.length_map] at h
    exact h.trans (Nat.pow_le_pow_left (by omega) 3)
  change binaryRankProgramsActions ((binaryNativeBranchTableRun plans xs).programs++
    (binaryAlignmentRun plans binaryNativePivotEndpoint binaryNativeNextEndpoint xs []).programs)≤_
  rw [binaryRankProgramsActions_append]
  calc
    _≤204*(k+4)^6*xs.length+2*(51*(k+4)^6)*xs.length := Nat.add_le_add hb ha
    _=306*(k+4)^6*xs.length := by ring
    _≤306*(k+4)^6*(k+4)^3 := Nat.mul_le_mul_left _ hl
    _=306*(k+4)^9 := by ring


def binaryNativeStageRun (k : ℕ) : BinaryGeneratedRun (originalWireCount (k+1)) :=
  let active:=binaryNativeOccupationRun k
  ⟨⟨prefixCode (active_available k) active.result.word,active.result.work⟩,active.programs⟩


theorem binaryNativeStageRun_result (k : ℕ) :
    (binaryNativeStageRun k).result=preparedNativeStageRun k := by
  simp only [binaryNativeStageRun,preparedNativeStageRun,binaryNativeOccupationRun_result]


def binaryNativeCompressionRun : (k : ℕ) → BinaryGeneratedRun (originalWireCount k)
  | 0 => ⟨⟨[],fun _ => 0⟩,[]⟩
  | k+1 =>
    let previous:=binaryNativeCompressionRun k
    let stage:=binaryNativeStageRun k
    ⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.result.word)++stage.result.word,
      fun i => previous.result.work i+stage.result.work i⟩,previous.programs++stage.programs⟩


theorem binaryNativeCompressionRun_result (k : ℕ) :
    (binaryNativeCompressionRun k).result=preparedNativeCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [binaryNativeCompressionRun,preparedNativeCompressionRun,binaryNativeStageRun_result,ih]


theorem binaryNativeCompressionRun_encodingActions (k : ℕ) :
    (binaryNativeCompressionRun k).encodingActions≤306*k*(k+4)^9 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs:=binaryNativeOccupationRun_encodingActions k
    have hp:=Nat.pow_le_pow_left (show k+4≤k+1+4 by omega) 9
    have hi':=ih.trans (Nat.mul_le_mul_left (306*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 306 hp)
    change binaryRankProgramsActions ((binaryNativeCompressionRun k).programs++(binaryNativeStageRun k).programs)≤_
    rw [binaryRankProgramsActions_append]
    exact (Nat.add_le_add hi' hs').trans_eq (by ring)


def binaryNativeDescriptorRun (k : ℕ) : BinaryGeneratedRun (originalWireCount k) :=
  let compression:=binaryNativeCompressionRun k
  ⟨⟨compression.result.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.result.work⟩,
    compression.programs⟩

/-- Entire descriptor-generation record: word and all previous rank-work fields. -/
theorem binaryNativeDescriptorRun_result (k : ℕ) :
    (binaryNativeDescriptorRun k).result=preparedNativeDescriptorRun k := by
  simp only [binaryNativeDescriptorRun,preparedNativeDescriptorRun,binaryNativeCompressionRun_result]


theorem binaryNativeDescriptorRun_encodingActions (k : ℕ) :
    (binaryNativeDescriptorRun k).encodingActions≤306*k*(k+4)^9 :=
  binaryNativeCompressionRun_encodingActions k

end EffectiveEncoding
