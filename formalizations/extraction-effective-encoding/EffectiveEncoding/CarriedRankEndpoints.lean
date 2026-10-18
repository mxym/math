import EffectiveEncoding.CarriedOccupationRank

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The child index uses the carried triple with one native coordinate
subtraction. The erased occupation occurs only in the erased proof/type. -/
def carriedBranchEndpoint {k : ℕ} (x : CarriedOccupation (k+1))
    (a : {a : Fin 4 // a∈x.occupation}) : EncodedEndpoint (2+codeWires k) :=
  let t:=erasedTriple x.triple a.1
  let child:=carriedEncodedEndpoint k t (by
    have ht : t=toTriple (x.occupation.erase a.1 a.2) := by
      simp only [t,x.triple_eq,erasedTriple_toTriple]
    rw [ht]
    exact toTriple_le _)
  ⟨packBits (Fin.append (letterBits a.1) (unpackBits child.point)),child.work⟩


theorem carriedBranchEndpoint_eq {k : ℕ} (x : CarriedOccupation (k+1))
    (a : {a : Fin 4 // a∈x.occupation}) :
    carriedBranchEndpoint x a=encodedBranchEndpoint x.occupation a := by
  have ht : erasedTriple x.triple a.1=toTriple (x.occupation.erase a.1 a.2) := by
    rw [x.triple_eq,erasedTriple_toTriple]
  simp only [carriedBranchEndpoint,encodedBranchEndpoint]
  simp only [carriedEncodedEndpoint_eq _ _ ht]


def carriedNextEndpoint {k : ℕ} (x : CarriedOccupation (k+1)) : EncodedEndpoint (2+codeWires k) :=
  let child:=carriedEncodedEndpoint (k+1) x.triple (by rw [x.triple_eq];exact toTriple_le _)
  ⟨packBits (extendBits (codeWires_step k) (unpackBits child.point)),child.work⟩


theorem carriedNextEndpoint_eq {k : ℕ} (x : CarriedOccupation (k+1)) :
    carriedNextEndpoint x=encodedNextEndpoint x.occupation := by
  simp only [carriedNextEndpoint,encodedNextEndpoint]
  simp only [carriedEncodedEndpoint_eq _ _ x.triple_eq]


def carriedPivotEndpoint {k : ℕ} (x : CarriedOccupation (k+1)) : EncodedEndpoint (2+codeWires k) :=
  carriedBranchEndpoint x (occupiedPivot x.occupation)


theorem carriedPivotEndpoint_eq {k : ℕ} (x : CarriedOccupation (k+1)) :
    carriedPivotEndpoint x=encodedPivotEndpoint x.occupation :=
  carriedBranchEndpoint_eq x _

/-- Occupied-letter selection still uses the literal occupation. All endpoint
rank inputs and branch masses instead read carried integers, with no count
callback or child multiset construction on these runtime paths. -/
def carriedBranchRun {k : ℕ} (x : CarriedOccupation (k+1)) : RankedBranchRun (2+codeWires k) :=
  let ν:=x.occupation
  rankedIndexedRun (by omega) (carriedBranchEndpoint x) (fun a => carriedMass x a.1)
    (occupiedPivot ν) (k+1)


theorem carriedBranchRun_eq {k : ℕ} (x : CarriedOccupation (k+1)) :
    carriedBranchRun x=rankedBranchRun x.occupation := by
  have he : carriedBranchEndpoint x=encodedBranchEndpoint x.occupation :=
    funext (carriedBranchEndpoint_eq x)
  simp only [carriedBranchRun,rankedBranchRun,he,carriedMass_value]

/-- The record list is traversed directly. This pullback theorem only relates
its erased word/result to the old semantic occupation traversal. -/
theorem rankedAlignmentRun_map_result {α β : Type*} {n : ℕ} (hn : 0<n)
    (E F : α → EncodedEndpoint n) (e f : β ↪ Bits n) (g : α → β)
    (hE : ∀ a,(E a).point=packBits (e (g a))) (hF : ∀ a,(F a).point=packBits (f (g a)))
    (xs : List α) (ss : List (PackedBits n×PackedBits n)) :
    (rankedAlignmentRun hn E F xs ss).result=packedAlignmentRun hn e f (xs.map g) ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [rankedAlignmentRun,packedAlignmentRun,List.map_cons,hE,hF,ih]


def carriedAlignmentRun {k : ℕ} (xs : List (CarriedOccupation (k+1))) : RankedAlignmentRun (2+codeWires k) :=
  rankedAlignmentRun (by omega) carriedPivotEndpoint carriedNextEndpoint xs []


theorem carriedAlignmentRun_result {k : ℕ} (xs : List (CarriedOccupation (k+1))) :
    (carriedAlignmentRun xs).result=packedAlignmentRun (by omega)
      (pivotEmbedding (constructedCompactEncoding k)) (constructedNextEncoding k)
      (xs.map CarriedOccupation.occupation) [] := by
  apply rankedAlignmentRun_map_result
  · intro x
    rw [carriedPivotEndpoint_eq,encodedPivotEndpoint_value]
  · intro x
    rw [carriedNextEndpoint_eq,encodedNextEndpoint_value]


theorem carriedAlignmentRun_work {k : ℕ} (xs : List (CarriedOccupation (k+1))) (i : Fin 3) :
    (carriedAlignmentRun xs).work i≤2*(rankWorkConstant i*(k+2)^3)*xs.length := by
  apply rankedAlignmentRun_work
  · intro x
    rw [carriedPivotEndpoint_eq]
    exact encodedPivotEndpoint_work _ i
  · intro x
    rw [carriedNextEndpoint_eq]
    exact encodedNextEndpoint_work _ i

end EffectiveEncoding
