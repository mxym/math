import EffectiveEncoding.NativeOccupationSelection

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def nativeBranchEndpoint {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) : EncodedEndpoint (2+codeWires k) :=
  let t:=erasedTriple x.1 a.1
  let child:=carriedEncodedEndpoint k t (by
    have ht : t=toTriple ((nativeOccupationValue x).erase a.1 a.2) := by
      change erasedTriple x.1 a.1=_
      rw [← toTriple_fromTriple (k+1) x.1 x.2]
      exact erasedTriple_toTriple _ a
    rw [ht]
    exact toTriple_le _)
  ⟨packBits (Fin.append (letterBits a.1) (unpackBits child.point)),child.work⟩


theorem nativeBranchEndpoint_eq {k : ℕ} (x : NativeOccupation (k+1))
    (a : {a : Fin 4 // a∈nativeOccupationValue x}) :
    nativeBranchEndpoint x a=encodedBranchEndpoint (nativeOccupationValue x) a := by
  have ht : erasedTriple x.1 a.1=toTriple ((nativeOccupationValue x).erase a.1 a.2) := by
    rw [← toTriple_fromTriple (k+1) x.1 x.2]
    exact erasedTriple_toTriple _ a
  simp only [nativeBranchEndpoint,encodedBranchEndpoint,carriedEncodedEndpoint_eq _ _ ht]


def nativeNextEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : EncodedEndpoint (2+codeWires k) :=
  let child:=carriedEncodedEndpoint (k+1) x.1 x.2
  ⟨packBits (extendBits (codeWires_step k) (unpackBits child.point)),child.work⟩


theorem nativeNextEndpoint_eq {k : ℕ} (x : NativeOccupation (k+1)) :
    nativeNextEndpoint x=encodedNextEndpoint (nativeOccupationValue x) := by
  simp only [nativeNextEndpoint,encodedNextEndpoint,
    carriedEncodedEndpoint_eq _ _ (toTriple_fromTriple (k+1) x.1 x.2).symm]
  rfl


def nativePivotEndpoint {k : ℕ} (x : NativeOccupation (k+1)) : EncodedEndpoint (2+codeWires k) :=
  nativeBranchEndpoint x (nativeOccupiedPivot x)


theorem nativePivotEndpoint_eq {k : ℕ} (x : NativeOccupation (k+1)) :
    nativePivotEndpoint x=encodedPivotEndpoint (nativeOccupationValue x) := by
  simp only [nativePivotEndpoint,encodedPivotEndpoint,nativeBranchEndpoint_eq,nativeOccupiedPivot_eq]

/-- The occupied-type index is semantic/proof-only. The explicitly installed
Fintype enumerates only native positivity checks on the four retained counts;
the endpoint, pivot and mass programs contain no semantic occupation values. -/
def nativeBranchRun {k : ℕ} (x : NativeOccupation (k+1)) : RankedBranchRun (2+codeWires k) :=
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  rankedIndexedRun (by omega) (nativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1)


theorem nativeBranchRun_eq {k : ℕ} (x : NativeOccupation (k+1)) :
    nativeBranchRun x=rankedBranchRun (nativeOccupationValue x) := by
  have hf : nativeOccupiedFintype x=
      (inferInstance : Fintype {a : Fin 4 // a∈nativeOccupationValue x}) := Subsingleton.elim _ _
  have he : nativeBranchEndpoint x=encodedBranchEndpoint (nativeOccupationValue x) :=
    funext (nativeBranchEndpoint_eq x)
  unfold nativeBranchRun
  change @rankedIndexedRun _ (nativeOccupiedFintype x) _ _ _ _ _ _ _=_
  rw [hf]
  simp only [rankedBranchRun,he,nativeMass_value,nativeOccupiedPivot_eq]

end EffectiveEncoding
