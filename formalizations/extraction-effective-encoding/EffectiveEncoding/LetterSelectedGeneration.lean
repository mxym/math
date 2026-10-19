import EffectiveEncoding.ListOccupationBranch
import EffectiveEncoding.PlannedCandidateGeneration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev AcceptedOccupationTableRecord := Sigma AcceptedOccupationTableResult

structure LetterSelectedCandidateResult (n : ℕ) where
  common : PlannedCandidateResult n
  tables : List AcceptedOccupationTableRecord

/-- One actual Boolean context and one actual retained occupation enumeration.
 Each accepted total/count-word selector is executed once; its same ordered
 letters feed both branch and stored-swap pivot selection. The old four-letter
 Finset/filter/sort/minimum path is absent from this runtime definition. -/
def letterSelectedOccupationRun (k : ℕ) : LetterSelectedCandidateResult (2+codeWires k) :=
  let context:=booleanMaskContextProgram (by omega : 0<2+codeWires k)
  let table:=acceptedOccupationTableProgram (k+1)
  let h:=acceptedOccupationTableProgram_sorted (k+1)
  let branches:=storedLettersBranchTableRun context.common.plans table.items h
  let aligned:=storedLettersAlignmentRun context.common.plans table.items h []
  ⟨⟨⟨⟨branches.word++aligned.word,branches.ranks++aligned.ranks,[table.enumeration.common]⟩,
    [⟨2+codeWires k,context.common⟩]⟩,[⟨2+codeWires k,context⟩]⟩,[⟨k+1,table⟩]⟩

/-- Entire public common generation/context record is preserved, including all
 enumeration, rank, mask and plan-table traces. This is not a word-only bridge. -/
theorem letterSelectedOccupationRun_common (k : ℕ) :
    (letterSelectedOccupationRun k).common=plannedCandidateOccupationRun k := by
  simp only [letterSelectedOccupationRun,storedLettersBranchTableRun_common,storedLettersAlignmentRun_common,
    acceptedOccupationTableProgram_native]
  change ⟨⟨⟨_,_,[(retainedTriplesProgram (k+1)).common]⟩,_⟩,_⟩=plannedCandidateOccupationRun k
  rw [retainedTriplesProgram_common]
  rfl

/-- Additional actual selector records only; their upstream range/product/
 filter traces already occur in common and are not charged twice. -/
def LetterSelectedCandidateResult.letterActions {n : ℕ} (r : LetterSelectedCandidateResult n) : ℕ :=
  (r.tables.map (fun p => p.2.letterActions)).sum


theorem letterSelectedOccupationRun_letterActions (k : ℕ) :
    (letterSelectedOccupationRun k).letterActions≤55*(k+5)^4 := by
  have hs:=acceptedOccupationTableProgram_letterActions (k+1)
  have hp:=Nat.pow_le_pow_left (show k+1+1≤k+5 by omega) 3
  have hf : 26*(k+1+4)+29≤55*(k+5) := by omega
  change (acceptedOccupationTableProgram (k+1)).letterActions+0≤_
  have h : (acceptedOccupationTableProgram (k+1)).letterActions≤55*(k+5)^4 :=
    hs.trans ((Nat.mul_le_mul hp hf).trans_eq (by ring))
  simpa only [Nat.add_zero] using h


def letterSelectedStageRun (k : ℕ) : LetterSelectedCandidateResult (originalWireCount (k+1)) :=
  let active:=letterSelectedOccupationRun k
  ⟨⟨⟨⟨prefixCode (active_available k) active.common.common.generation.word,
    active.common.common.generation.ranks,active.common.common.generation.stageTables⟩,
    active.common.common.masks⟩,active.common.contexts⟩,active.tables⟩


theorem letterSelectedStageRun_common (k : ℕ) :
    (letterSelectedStageRun k).common=plannedCandidateStageRun k := by
  simp only [letterSelectedStageRun,letterSelectedOccupationRun_common,plannedCandidateStageRun]


def letterSelectedCompressionRun : (k : ℕ) → LetterSelectedCandidateResult (originalWireCount k)
  | 0 => ⟨⟨⟨⟨[],[],[]⟩,[]⟩,[]⟩,[]⟩
  | k+1 =>
    let previous:=letterSelectedCompressionRun k
    let stage:=letterSelectedStageRun k
    ⟨⟨⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.common.common.generation.word)++
      stage.common.common.generation.word,previous.common.common.generation.ranks++stage.common.common.generation.ranks,
      previous.common.common.generation.stageTables++stage.common.common.generation.stageTables⟩,
      previous.common.common.masks++stage.common.common.masks⟩,previous.common.contexts++stage.common.contexts⟩,
      previous.tables++stage.tables⟩


theorem letterSelectedCompressionRun_common (k : ℕ) :
    (letterSelectedCompressionRun k).common=plannedCandidateCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [letterSelectedCompressionRun,plannedCandidateCompressionRun,letterSelectedStageRun_common,ih]


theorem letterSelectedCompressionRun_letterActions (k : ℕ) :
    (letterSelectedCompressionRun k).letterActions≤55*k*(k+5)^4 := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    have hs:=letterSelectedOccupationRun_letterActions k
    have hp:=Nat.pow_le_pow_left (show k+5≤k+1+5 by omega) 4
    have hi':=ih.trans (Nat.mul_le_mul_left (55*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 55 hp)
    change (((letterSelectedCompressionRun k).tables++(letterSelectedStageRun k).tables).map
      (fun p => p.2.letterActions)).sum≤_
    rw [List.map_append,List.sum_append]
    exact (Nat.add_le_add hi' hs').trans_eq (by ring)


def letterSelectedDescriptorRun (k : ℕ) : LetterSelectedCandidateResult (originalWireCount k) :=
  let compression:=letterSelectedCompressionRun k
  ⟨⟨⟨⟨compression.common.common.generation.word++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),
    compression.common.common.generation.ranks,compression.common.common.generation.stageTables⟩,
    compression.common.common.masks⟩,compression.common.contexts⟩,compression.tables⟩


theorem letterSelectedDescriptorRun_common (k : ℕ) :
    (letterSelectedDescriptorRun k).common=plannedCandidateDescriptorRun k := by
  simp only [letterSelectedDescriptorRun,letterSelectedCompressionRun_common,plannedCandidateDescriptorRun]


theorem letterSelectedDescriptorRun_word (k : ℕ) :
    (letterSelectedDescriptorRun k).common.common.generation.word=extractionCode k := by
  rw [letterSelectedDescriptorRun_common,plannedCandidateDescriptorRun_word]


theorem letterSelectedDescriptorRun_letterActions (k : ℕ) :
    (letterSelectedDescriptorRun k).letterActions≤55*k*(k+5)^4 :=
  letterSelectedCompressionRun_letterActions k

end EffectiveEncoding
