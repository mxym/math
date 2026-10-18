import EffectiveEncoding.RankedAlignmentWork

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The recursive traversal stores each branch run once and combines the
returned word and rank annotations. -/
def rankedBranchTableRun {k : ℕ} : List (Sym (Fin 4) (k+1)) → RankedBranchRun (2+codeWires k)
  | [] => ⟨[],fun _ => 0⟩
  | ν::νs =>
    let branch:=rankedBranchRun ν
    let tail:=rankedBranchTableRun νs
    ⟨branch.word++tail.word,fun i => branch.work i+tail.work i⟩


theorem rankedBranchTableRun_word {k : ℕ} (xs : List (Sym (Fin 4) (k+1))) :
    (rankedBranchTableRun xs).word=xs.flatMap (branchCode (constructedCompactEncoding k)) := by
  induction xs with
  | nil => rfl
  | cons ν xs ih => simp only [rankedBranchTableRun,List.flatMap_cons,rankedBranchRun_word,ih]


theorem rankedBranchTableRun_work {k : ℕ} (xs : List (Sym (Fin 4) (k+1))) (i : Fin 3) :
    (rankedBranchTableRun xs).work i≤4*(rankWorkConstant i*(k+2)^3)*xs.length := by
  induction xs with
  | nil => simp [rankedBranchTableRun]
  | cons ν xs ih =>
    have h:=(rankedBranchRun_work ν i).trans
      (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show k+1≤k+2 by omega) 3)))
    change (rankedBranchRun ν).work i+(rankedBranchTableRun xs).work i≤_
    calc
      _≤4*(rankWorkConstant i*(k+2)^3)+4*(rankWorkConstant i*(k+2)^3)*xs.length := Nat.add_le_add h ih
      _=4*(rankWorkConstant i*(k+2)^3)*(ν::xs).length := by simp only [List.length_cons];ring

/-- Build the occupation table once, then execute rank-returning endpoints
in the branch and alignment traversals over that same table. -/
def rankedOccupationRun (k : ℕ) : RankedBranchRun (2+codeWires k) :=
  let occupationsHere:=(literalOccupationTable (k+1)).occupations
  let branches:=rankedBranchTableRun occupationsHere
  let aligned:=rankedAlignmentRun (by omega) encodedPivotEndpoint encodedNextEndpoint occupationsHere []
  ⟨branches.word++aligned.result.word,fun i => branches.work i+aligned.work i⟩


theorem rankedOccupationRun_word (k : ℕ) :
    (rankedOccupationRun k).word=
      literalPackedOccupationStepCode (constructedCompactEncoding k) (constructedNextEncoding k) := by
  simp only [rankedOccupationRun,literalPackedOccupationStepCode,rankedBranchTableRun_word,
    rankedAlignmentRun_result _ _ _ _ _ encodedPivotEndpoint_value encodedNextEndpoint_value]


theorem rankedOccupationRun_work (k : ℕ) (i : Fin 3) :
    (rankedOccupationRun k).work i≤6*rankWorkConstant i*(k+2)^6 := by
  let xs:=(literalOccupationTable (k+1)).occupations
  have hb:=rankedBranchTableRun_work xs i
  have ha:=rankedAlignmentRun_work (by omega) encodedPivotEndpoint encodedNextEndpoint
    xs [] i (rankWorkConstant i*(k+2)^3)
    (fun ν => encodedPivotEndpoint_work ν i) (fun ν => encodedNextEndpoint_work ν i)
  have hl : xs.length≤(k+2)^3 := by
    simp only [xs,literalOccupationTable_value,builtOccupations_eq]
    simpa only [Nat.add_assoc,Nat.reduceAdd] using enumeration_candidate_bound (k+1)
  change (rankedBranchTableRun xs).work i+
    (rankedAlignmentRun (by omega) encodedPivotEndpoint encodedNextEndpoint xs []).work i≤_
  calc
    _≤4*(rankWorkConstant i*(k+2)^3)*xs.length+2*(rankWorkConstant i*(k+2)^3)*xs.length := Nat.add_le_add hb ha
    _=6*rankWorkConstant i*(k+2)^3*xs.length := by ring
    _≤6*rankWorkConstant i*(k+2)^3*(k+2)^3 := Nat.mul_le_mul_left _ hl
    _=6*rankWorkConstant i*(k+2)^6 := by ring


def rankedStageRun (k : ℕ) : RankedBranchRun (originalWireCount (k+1)) :=
  let active:=rankedOccupationRun k
  ⟨prefixCode (active_available k) active.word,active.work⟩


theorem rankedStageRun_word (k : ℕ) : (rankedStageRun k).word=literalStageCode k := by
  simp only [rankedStageRun,literalStageCode,rankedOccupationRun_word]


def rankedCompressionRun : (k : ℕ) → RankedBranchRun (originalWireCount k)
  | 0 => ⟨[],fun _ => 0⟩
  | k+1 =>
    let previous:=rankedCompressionRun k
    let stage:=rankedStageRun k
    ⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      fun i => previous.work i+stage.work i⟩


theorem rankedCompressionRun_word (k : ℕ) :
    (rankedCompressionRun k).word=literalCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rankedCompressionRun,literalCompressionCode,rankedStageRun_word,ih]


theorem rankedCompressionRun_work (k : ℕ) (i : Fin 3) :
    (rankedCompressionRun k).work i≤6*rankWorkConstant i*k*(k+2)^6 := by
  induction k with
  | zero => simp [rankedCompressionRun]
  | succ k ih =>
    have hp : (rankedCompressionRun k).work i≤6*rankWorkConstant i*k*(k+3)^6 := by
      exact ih.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show k+2≤k+3 by omega) 6))
    have hs:=rankedOccupationRun_work k i
    have hs' : (rankedStageRun k).work i≤6*rankWorkConstant i*(k+3)^6 := by
      exact hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show k+2≤k+3 by omega) 6))
    change (rankedCompressionRun k).work i+(rankedStageRun k).work i≤_
    calc
      _≤6*rankWorkConstant i*k*(k+3)^6+6*rankWorkConstant i*(k+3)^6 := Nat.add_le_add hp hs'
      _=6*rankWorkConstant i*(k+1)*(k+1+2)^6 := by ring


def rankedDescriptorRun (k : ℕ) : RankedBranchRun (originalWireCount k) :=
  let compression:=rankedCompressionRun k
  ⟨compression.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),compression.work⟩


theorem rankedDescriptorRun_word (k : ℕ) : (rankedDescriptorRun k).word=literalExtractionCode k := by
  simp only [rankedDescriptorRun,literalExtractionCode,rankedCompressionRun_word]


theorem rankedDescriptorRun_work (k : ℕ) (i : Fin 3) :
    (rankedDescriptorRun k).work i≤6*rankWorkConstant i*k*(k+2)^6 :=
  rankedCompressionRun_work k i

end EffectiveEncoding
