import EffectiveEncoding.NativeBinaryRankEndpoints
import EffectiveEncoding.PreparedNativeGeneration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev BinaryRankProgramRecord := Sigma NativeBinaryRankResult

/-- Sum of actual retained increment/trim/output-digit traces only. -/
def binaryRankProgramsActions (xs : List BinaryRankProgramRecord) : ℕ :=
  (xs.map (fun r => r.2.encodingActions)).sum


theorem binaryRankProgramsActions_append (xs ys : List BinaryRankProgramRecord) :
    binaryRankProgramsActions (xs++ys)=binaryRankProgramsActions xs+binaryRankProgramsActions ys := by
  simp only [binaryRankProgramsActions,List.map_append,List.sum_append]


theorem binaryRankProgramsActions_flatMap {α : Type*} (f : α → List BinaryRankProgramRecord) (xs : List α) :
    binaryRankProgramsActions (xs.flatMap f)=(xs.map (fun a => binaryRankProgramsActions (f a))).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons,binaryRankProgramsActions_append,ih,List.map_cons,List.sum_cons]

structure BinaryEncodedEndpoint (n : ℕ) where
  endpoint : EncodedEndpoint n
  programs : List BinaryRankProgramRecord


def BinaryEncodedEndpoint.encodingActions {n : ℕ} (r : BinaryEncodedEndpoint n) : ℕ :=
  binaryRankProgramsActions r.programs

/-- Real child rank-word execution retained beside the packed branch endpoint. -/
def binaryNativeBranchEndpoint {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) : BinaryEncodedEndpoint (2+codeWires k) :=
  let t:=erasedTriple x.1 a.1
  let child:=nativeBinaryRankProgram k t (by
    have ht : t=toTriple ((nativeOccupationValue x).erase a.1 a.2) := by
      change erasedTriple x.1 a.1=_
      rw [←toTriple_fromTriple (k+1) x.1 x.2]
      exact erasedTriple_toTriple _ a
    rw [ht]
    exact toTriple_le _)
  ⟨⟨packBits (Fin.append (letterBits a.1) (unpackBits child.erase.point)),child.erase.work⟩,[⟨k,child⟩]⟩


theorem binaryNativeBranchEndpoint_endpoint {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (binaryNativeBranchEndpoint x a).endpoint=nativeBranchEndpoint x a := by
  simp only [binaryNativeBranchEndpoint,nativeBinaryRankProgram_erase,nativeBranchEndpoint]


theorem binaryNativeBranchEndpoint_encodingActions {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    (binaryNativeBranchEndpoint x a).encodingActions≤51*(k+3)^6 := by
  simp only [binaryNativeBranchEndpoint,BinaryEncodedEndpoint.encodingActions,binaryRankProgramsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact nativeBinaryRankProgram_encodingActions_polynomial _ _ _


def binaryNativeNextEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : BinaryEncodedEndpoint (2+codeWires k) :=
  let child:=nativeBinaryRankProgram (k+1) x.1 x.2
  ⟨⟨packBits (extendBits (codeWires_step k) (unpackBits child.erase.point)),child.erase.work⟩,[⟨k+1,child⟩]⟩


theorem binaryNativeNextEndpoint_endpoint {k : ℕ} (x : NativeOccupation (k+1)) :
    (binaryNativeNextEndpoint x).endpoint=nativeNextEndpoint x := by
  simp only [binaryNativeNextEndpoint,nativeBinaryRankProgram_erase,nativeNextEndpoint]


theorem binaryNativeNextEndpoint_encodingActions {k : ℕ} (x : NativeOccupation (k+1)) :
    (binaryNativeNextEndpoint x).encodingActions≤51*(k+4)^6 := by
  simpa only [binaryNativeNextEndpoint,BinaryEncodedEndpoint.encodingActions,binaryRankProgramsActions,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd] using
    nativeBinaryRankProgram_encodingActions_polynomial (k+1) x.1 x.2


def binaryNativePivotEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : BinaryEncodedEndpoint (2+codeWires k) :=
  binaryNativeBranchEndpoint x (nativeOccupiedPivot x)


theorem binaryNativePivotEndpoint_endpoint {k : ℕ} (x : NativeOccupation (k+1)) :
    (binaryNativePivotEndpoint x).endpoint=nativePivotEndpoint x :=
  binaryNativeBranchEndpoint_endpoint x (nativeOccupiedPivot x)


theorem binaryNativePivotEndpoint_encodingActions {k : ℕ} (x : NativeOccupation (k+1)) :
    (binaryNativePivotEndpoint x).encodingActions≤51*(k+4)^6 :=
  (binaryNativeBranchEndpoint_encodingActions x (nativeOccupiedPivot x)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))

end EffectiveEncoding
