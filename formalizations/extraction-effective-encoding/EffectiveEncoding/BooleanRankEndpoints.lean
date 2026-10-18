import EffectiveEncoding.NativeBooleanRankProgram
import EffectiveEncoding.BinaryRankGenerationRecords

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev BooleanRankRecord := Sigma NativeBooleanRankResult

def booleanRankRecordsActions (xs : List BooleanRankRecord) : ℕ :=
  (xs.map (fun r => r.2.booleanActions)).sum


theorem booleanRankRecordsActions_append (xs ys : List BooleanRankRecord) :
    booleanRankRecordsActions (xs++ys)=booleanRankRecordsActions xs+booleanRankRecordsActions ys := by
  simp only [booleanRankRecordsActions,List.map_append,List.sum_append]

structure ScannedRankWord (k : ℕ) where
  scan : NativeBooleanRankResult k
  word : NativeBinaryRankResult k

/-- The stored rank index comes from the actual Boolean comparison scan.
Its real binary increment/trim/padding execution follows once. -/
def scannedRankWordProgram (k : ℕ) (t : Triple) (h : total t≤k) : ScannedRankWord k :=
  let scan:=nativeBooleanRankProgram k t h
  let encoded:=unaryWordEncoding scan.ranked.index.val
  let output:=endpointBitsProgram (codeWires k) encoded.bits
  ⟨scan,⟨scan.ranked,encoded,output⟩⟩


theorem scannedRankWordProgram_word (k : ℕ) (t : Triple) (h : total t≤k) :
    (scannedRankWordProgram k t h).word=nativeBinaryRankProgram k t h := by
  simp only [scannedRankWordProgram,nativeBooleanRankProgram_ranked,nativeBinaryRankProgram]

structure ScannedEncodedEndpoint (n : ℕ) where
  binary : BinaryEncodedEndpoint n
  scans : List BooleanRankRecord


def ScannedEncodedEndpoint.scanActions {n : ℕ} (r : ScannedEncodedEndpoint n) : ℕ :=
  booleanRankRecordsActions r.scans


def scannedNativeBranchEndpoint {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) : ScannedEncodedEndpoint (2+codeWires k) :=
  let t:=erasedTriple x.1 a.1
  let child:=scannedRankWordProgram k t (by
    have ht : t=toTriple ((nativeOccupationValue x).erase a.1 a.2) := by
      change erasedTriple x.1 a.1=_
      rw [←toTriple_fromTriple (k+1) x.1 x.2]
      exact erasedTriple_toTriple _ a
    rw [ht]
    exact toTriple_le _)
  ⟨⟨⟨packBits (Fin.append (letterBits a.1) (unpackBits child.word.erase.point)),child.word.erase.work⟩,
    [⟨k,child.word⟩]⟩,[⟨k,child.scan⟩]⟩


theorem scannedNativeBranchEndpoint_binary {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (scannedNativeBranchEndpoint x a).binary=binaryNativeBranchEndpoint x a := by
  simp only [scannedNativeBranchEndpoint,scannedRankWordProgram_word,binaryNativeBranchEndpoint]


theorem scannedNativeBranchEndpoint_scanActions {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (scannedNativeBranchEndpoint x a).scanActions≤300*(k+3)^5 := by
  simp only [scannedNativeBranchEndpoint,ScannedEncodedEndpoint.scanActions,booleanRankRecordsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,scannedRankWordProgram]
  exact (nativeBooleanRankProgram_booleanActions_polynomial _ _ _).trans
    (Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left (by omega) 5))


def scannedNativeNextEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : ScannedEncodedEndpoint (2+codeWires k) :=
  let child:=scannedRankWordProgram (k+1) x.1 x.2
  ⟨⟨⟨packBits (extendBits (codeWires_step k) (unpackBits child.word.erase.point)),child.word.erase.work⟩,
    [⟨k+1,child.word⟩]⟩,[⟨k+1,child.scan⟩]⟩


theorem scannedNativeNextEndpoint_binary {k : ℕ} (x : NativeOccupation (k+1)) :
    (scannedNativeNextEndpoint x).binary=binaryNativeNextEndpoint x := by
  simp only [scannedNativeNextEndpoint,scannedRankWordProgram_word,binaryNativeNextEndpoint]


theorem scannedNativeNextEndpoint_scanActions {k : ℕ} (x : NativeOccupation (k+1)) :
    (scannedNativeNextEndpoint x).scanActions≤300*(k+3)^5 := by
  simpa only [scannedNativeNextEndpoint,ScannedEncodedEndpoint.scanActions,booleanRankRecordsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,scannedRankWordProgram,
    Nat.add_assoc,Nat.reduceAdd] using nativeBooleanRankProgram_booleanActions_polynomial (k+1) x.1 x.2


def scannedNativePivotEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : ScannedEncodedEndpoint (2+codeWires k) :=
  scannedNativeBranchEndpoint x (nativeOccupiedPivot x)


theorem scannedNativePivotEndpoint_binary {k : ℕ} (x : NativeOccupation (k+1)) :
    (scannedNativePivotEndpoint x).binary=binaryNativePivotEndpoint x :=
  scannedNativeBranchEndpoint_binary x (nativeOccupiedPivot x)


theorem scannedNativePivotEndpoint_scanActions {k : ℕ} (x : NativeOccupation (k+1)) :
    (scannedNativePivotEndpoint x).scanActions≤300*(k+3)^5 :=
  scannedNativeBranchEndpoint_scanActions x (nativeOccupiedPivot x)

end EffectiveEncoding
