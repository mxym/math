import EffectiveEncoding.BinaryMaskPlanProgram
import EffectiveEncoding.CandidateDescriptorGeneration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev BinaryMaskRecord := Sigma BinaryMaskPlanResult

structure MaskedCandidateResult (n : ℕ) where
  generation : CandidateDescriptorResult n
  masks : List BinaryMaskRecord

/-- The actual saved binary mask program supplies the single shared context.
No old preparedMaskTable is executed to populate a compatibility field. -/
def maskedCandidateOccupationRun (k : ℕ) : MaskedCandidateResult (2+codeWires k) :=
  let context:=binaryMaskPlanProgram (by omega : 0<2+codeWires k)
  let table:=candidateNativeTableProgram (k+1)
  let branches:=candidateBranchTableRun context.plans table.items
  let aligned:=candidateAlignmentRun context.plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []
  ⟨⟨branches.word++aligned.word,branches.ranks++aligned.ranks,[table.enumeration]⟩,[⟨2+codeWires k,context⟩]⟩

/-- Whole common generation record equality follows from the actual exact
plan list, not merely from a word or matrix interpretation equality. The new
mask-construction records remain separately retained. -/
theorem maskedCandidateOccupationRun_generation (k : ℕ) :
    (maskedCandidateOccupationRun k).generation=candidateOccupationRun k := by
  simp only [maskedCandidateOccupationRun,binaryMaskPlanProgram_plans,candidateOccupationRun]


def MaskedCandidateResult.maskActions {n : ℕ} (r : MaskedCandidateResult n) : ℕ :=
  (r.masks.map (fun p => p.2.actions)).sum


theorem maskedCandidateOccupationRun_maskActions (k : ℕ) :
    (maskedCandidateOccupationRun k).maskActions≤10592*(k+3)^6 := by
  simp only [maskedCandidateOccupationRun,MaskedCandidateResult.maskActions,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero]
  exact binaryMaskPlanProgram_active_actions k


def maskedCandidateStageRun (k : ℕ) : MaskedCandidateResult (originalWireCount (k+1)) :=
  let active:=maskedCandidateOccupationRun k
  ⟨⟨prefixCode (active_available k) active.generation.word,active.generation.ranks,
    active.generation.stageTables⟩,active.masks⟩


theorem maskedCandidateStageRun_generation (k : ℕ) :
    (maskedCandidateStageRun k).generation=candidateStageRun k := by
  simp only [maskedCandidateStageRun,maskedCandidateOccupationRun_generation,candidateStageRun]


def maskedCandidateCompressionRun : (k : ℕ) → MaskedCandidateResult (originalWireCount k)
  | 0 => ⟨⟨[],[],[]⟩,[]⟩
  | k+1 =>
    let previous:=maskedCandidateCompressionRun k
    let stage:=maskedCandidateStageRun k
    ⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.generation.word)++stage.generation.word,
      previous.generation.ranks++stage.generation.ranks,
      previous.generation.stageTables++stage.generation.stageTables⟩,
      previous.masks++stage.masks⟩


theorem maskedCandidateCompressionRun_generation (k : ℕ) :
    (maskedCandidateCompressionRun k).generation=candidateCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [maskedCandidateCompressionRun,candidateCompressionRun,maskedCandidateStageRun_generation,ih]


theorem maskedCandidateCompressionRun_maskActions (k : ℕ) :
    (maskedCandidateCompressionRun k).maskActions≤10592*k*(k+3)^6 := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    have hs:=maskedCandidateOccupationRun_maskActions k
    have hp:=Nat.pow_le_pow_left (show k+3≤k+1+3 by omega) 6
    have hi':=ih.trans (Nat.mul_le_mul_left (10592*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 10592 hp)
    change (((maskedCandidateCompressionRun k).masks++(maskedCandidateStageRun k).masks).map
      (fun p => p.2.actions)).sum≤_
    rw [List.map_append,List.sum_append]
    exact (Nat.add_le_add hi' hs').trans_eq (by ring)

/-- Complete executable descriptor generator using real Boolean range/filter
and binary mask digits. Common rank/table records and actual mask range/copy
records are retained from the same stage calls. -/
def maskedCandidateDescriptorRun (k : ℕ) : MaskedCandidateResult (originalWireCount k) :=
  let compression:=maskedCandidateCompressionRun k
  ⟨⟨compression.generation.word++
      castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),
    compression.generation.ranks,compression.generation.stageTables⟩,compression.masks⟩


theorem maskedCandidateDescriptorRun_generation (k : ℕ) :
    (maskedCandidateDescriptorRun k).generation=candidateDescriptorRun k := by
  simp only [maskedCandidateDescriptorRun,maskedCandidateCompressionRun_generation,candidateDescriptorRun]


theorem maskedCandidateDescriptorRun_word (k : ℕ) :
    (maskedCandidateDescriptorRun k).generation.word=extractionCode k := by
  rw [maskedCandidateDescriptorRun_generation,candidateDescriptorRun_extractionCode]


theorem maskedCandidateDescriptorRun_maskActions (k : ℕ) :
    (maskedCandidateDescriptorRun k).maskActions≤10592*k*(k+3)^6 :=
  maskedCandidateCompressionRun_maskActions k

/-- Only same-execution retained rank/table and binary mask range/copy models.
Finite-set/sort/Pauli-plan construction and remaining source control stay open. -/
def MaskedCandidateResult.accountedActions {n : ℕ} (r : MaskedCandidateResult n) : ℕ :=
  r.generation.actions+r.maskActions


theorem maskedCandidateDescriptorRun_accountedActions (k : ℕ) :
    (maskedCandidateDescriptorRun k).accountedActions≤
      3506*k*(k+5)^9+10592*k*(k+3)^6 := by
  unfold MaskedCandidateResult.accountedActions
  rw [maskedCandidateDescriptorRun_generation]
  exact Nat.add_le_add (candidateDescriptorRun_actions k) (maskedCandidateDescriptorRun_maskActions k)


theorem maskedCandidateDescriptorRun_accountedActions_polynomial (k : ℕ) :
    (maskedCandidateDescriptorRun k).accountedActions≤14098*k*(k+5)^9 := by
  have hp : (k+3)^6≤(k+5)^9 := (Nat.pow_le_pow_left (show k+3≤k+5 by omega) 6).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  apply (maskedCandidateDescriptorRun_accountedActions k).trans
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left (10592*k) hp) _).trans_eq (by ring)

end EffectiveEncoding
