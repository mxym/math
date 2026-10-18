import EffectiveEncoding.CarriedRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def carriedBranchTableRun {k : ℕ} : List (CarriedOccupation (k+1)) → RankedBranchRun (2+codeWires k)
  | [] => ⟨[],fun _ => 0⟩
  | x::xs =>
    let branch:=carriedBranchRun x
    let tail:=carriedBranchTableRun xs
    ⟨branch.word++tail.word,fun i => branch.work i+tail.work i⟩


theorem carriedBranchTableRun_eq {k : ℕ} (xs : List (CarriedOccupation (k+1))) :
    carriedBranchTableRun xs=rankedBranchTableRun (xs.map CarriedOccupation.occupation) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [carriedBranchTableRun,rankedBranchTableRun,List.map_cons,carriedBranchRun_eq,ih]


theorem rankedAlignmentRun_map_eq {α β : Type*} {n : ℕ} (hn : 0<n)
    (E F : α → EncodedEndpoint n) (e f : β → EncodedEndpoint n) (g : α → β)
    (hE : ∀ a,E a=e (g a)) (hF : ∀ a,F a=f (g a))
    (xs : List α) (ss : List (PackedBits n×PackedBits n)) :
    rankedAlignmentRun hn E F xs ss=rankedAlignmentRun hn e f (xs.map g) ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [rankedAlignmentRun,List.map_cons,hE,hF,ih]


theorem carriedAlignmentRun_eq {k : ℕ} (xs : List (CarriedOccupation (k+1))) :
    carriedAlignmentRun xs=rankedAlignmentRun (by omega) encodedPivotEndpoint encodedNextEndpoint
      (xs.map CarriedOccupation.occupation) [] :=
  rankedAlignmentRun_map_eq _ _ _ _ _ _ carriedPivotEndpoint_eq carriedNextEndpoint_eq _ _

/-- Retain the enumerated triples in the actual stage table. Neither branch
nor alignment ranking converts the literal occupation back into counts. -/
def carriedOccupationRun (k : ℕ) : RankedBranchRun (2+codeWires k) :=
  let occupationsHere:=carriedOccupationTable (k+1)
  let branches:=carriedBranchTableRun occupationsHere
  let aligned:=carriedAlignmentRun occupationsHere
  ⟨branches.word++aligned.result.word,fun i => branches.work i+aligned.work i⟩


theorem carriedOccupationRun_eq (k : ℕ) : carriedOccupationRun k=rankedOccupationRun k := by
  simp only [carriedOccupationRun,rankedOccupationRun,carriedBranchTableRun_eq,
    carriedAlignmentRun_eq,carriedOccupationTable_values]


def carriedStageRun (k : ℕ) : RankedBranchRun (originalWireCount (k+1)) :=
  let active:=carriedOccupationRun k
  ⟨prefixCode (active_available k) active.word,active.work⟩


theorem carriedStageRun_eq (k : ℕ) : carriedStageRun k=rankedStageRun k := by
  simp only [carriedStageRun,rankedStageRun,carriedOccupationRun_eq]


def carriedCompressionRun : (k : ℕ) → RankedBranchRun (originalWireCount k)
  | 0 => ⟨[],fun _ => 0⟩
  | k+1 =>
    let previous:=carriedCompressionRun k
    let stage:=carriedStageRun k
    ⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      fun i => previous.work i+stage.work i⟩


theorem carriedCompressionRun_eq (k : ℕ) : carriedCompressionRun k=rankedCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [carriedCompressionRun,rankedCompressionRun,carriedStageRun_eq,ih]


def carriedDescriptorRun (k : ℕ) : RankedBranchRun (originalWireCount k) :=
  let compression:=carriedCompressionRun k
  ⟨compression.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.work⟩


theorem carriedDescriptorRun_eq (k : ℕ) : carriedDescriptorRun k=rankedDescriptorRun k := by
  simp only [carriedDescriptorRun,rankedDescriptorRun,carriedCompressionRun_eq]


theorem carriedDescriptorRun_work (k : ℕ) (i : Fin 3) :
    (carriedDescriptorRun k).work i≤6*rankWorkConstant i*k*(k+2)^6 := by
  rw [carriedDescriptorRun_eq]
  exact rankedDescriptorRun_work k i

end EffectiveEncoding
