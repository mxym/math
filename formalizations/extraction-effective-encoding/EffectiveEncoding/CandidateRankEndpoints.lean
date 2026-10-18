import EffectiveEncoding.BinaryGeneratedRank
import EffectiveEncoding.BooleanRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev CandidateRankRecord := Sigma BinaryGeneratedRankResult

structure CandidateRankEndpoint (n : ℕ) where
  point : PackedBits n
  ranks : List CandidateRankRecord

def candidateNativeBranchEndpoint {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) : CandidateRankEndpoint (2+codeWires k) :=
  let t:=erasedTriple x.1 a.1
  let child:=binaryGeneratedRankProgram k t (by
    have ht : t=toTriple ((nativeOccupationValue x).erase a.1 a.2) := by
      change erasedTriple x.1 a.1=_
      rw [←toTriple_fromTriple (k+1) x.1 x.2]
      exact erasedTriple_toTriple _ a
    rw [ht]
    exact toTriple_le _)
  ⟨packBits (Fin.append (letterBits a.1) (unpackBits child.output.bits)),[⟨k,child⟩]⟩


def candidateNativeNextEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : CandidateRankEndpoint (2+codeWires k) :=
  let child:=binaryGeneratedRankProgram (k+1) x.1 x.2
  ⟨packBits (extendBits (codeWires_step k) (unpackBits child.output.bits)),[⟨k+1,child⟩]⟩


def candidateNativePivotEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : CandidateRankEndpoint (2+codeWires k) :=
  candidateNativeBranchEndpoint x (nativeOccupiedPivot x)

theorem candidateNativeBranchEndpoint_point {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (candidateNativeBranchEndpoint x a).point=(scannedNativeBranchEndpoint x a).binary.endpoint.point := by
  simp only [candidateNativeBranchEndpoint,binaryGeneratedRankProgram_output,scannedNativeBranchEndpoint,
    scannedRankWordProgram_word,nativeBinaryRankProgram,NativeBinaryRankResult.erase]


theorem candidateNativeNextEndpoint_point {k : ℕ} (x : NativeOccupation (k+1)) :
    (candidateNativeNextEndpoint x).point=(scannedNativeNextEndpoint x).binary.endpoint.point := by
  simp only [candidateNativeNextEndpoint,binaryGeneratedRankProgram_output,scannedNativeNextEndpoint,
    scannedRankWordProgram_word,nativeBinaryRankProgram,NativeBinaryRankResult.erase]


theorem candidateNativePivotEndpoint_point {k : ℕ} (x : NativeOccupation (k+1)) :
    (candidateNativePivotEndpoint x).point=(scannedNativePivotEndpoint x).binary.endpoint.point :=
  candidateNativeBranchEndpoint_point x (nativeOccupiedPivot x)


def candidateRankRecordsActions (xs : List CandidateRankRecord) : ℕ :=
  (xs.map (fun r => r.2.actions)).sum


theorem candidateRankRecordsActions_append (xs ys : List CandidateRankRecord) :
    candidateRankRecordsActions (xs++ys)=candidateRankRecordsActions xs+candidateRankRecordsActions ys := by
  simp only [candidateRankRecordsActions,List.map_append,List.sum_append]


def CandidateRankEndpoint.actions {n : ℕ} (r : CandidateRankEndpoint n) : ℕ :=
  candidateRankRecordsActions r.ranks


theorem candidateNativeBranchEndpoint_actions {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (candidateNativeBranchEndpoint x a).actions≤551*(k+5)^6 := by
  simp only [candidateNativeBranchEndpoint,CandidateRankEndpoint.actions,candidateRankRecordsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact (binaryGeneratedRankProgram_actions_polynomial _ _ _).trans
    (Nat.mul_le_mul_left 551 (Nat.pow_le_pow_left (by omega) 6))


theorem candidateNativeNextEndpoint_actions {k : ℕ} (x : NativeOccupation (k+1)) :
    (candidateNativeNextEndpoint x).actions≤551*(k+5)^6 := by
  simp only [candidateNativeNextEndpoint,CandidateRankEndpoint.actions,candidateRankRecordsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact (binaryGeneratedRankProgram_actions_polynomial _ _ _).trans
    (Nat.mul_le_mul_left 551 (Nat.pow_le_pow_left (by omega) 6))


theorem candidateNativePivotEndpoint_actions {k : ℕ} (x : NativeOccupation (k+1)) :
    (candidateNativePivotEndpoint x).actions≤551*(k+5)^6 :=
  candidateNativeBranchEndpoint_actions x (nativeOccupiedPivot x)

end EffectiveEncoding
