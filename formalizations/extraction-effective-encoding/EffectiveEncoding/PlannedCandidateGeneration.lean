import EffectiveEncoding.BooleanMaskContextProgram
import EffectiveEncoding.MaskedCandidateGeneration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev BooleanContextRecord := Sigma BooleanMaskContextResult

structure PlannedCandidateResult (n : ℕ) where
  common : MaskedCandidateResult n
  contexts : List BooleanContextRecord

/-- Each stage actually builds one Boolean/list context, then uses that same
stored plan list for all branches and stored-swap alignment. The common mask
record and newly charged plan records reference this same actual context. -/
def plannedCandidateOccupationRun (k : ℕ) : PlannedCandidateResult (2+codeWires k) :=
  let context:=booleanMaskContextProgram (by omega : 0<2+codeWires k)
  let table:=candidateNativeTableProgram (k+1)
  let branches:=candidateBranchTableRun context.common.plans table.items
  let aligned:=candidateAlignmentRun context.common.plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []
  ⟨⟨⟨branches.word++aligned.word,branches.ranks++aligned.ranks,[table.enumeration]⟩,
    [⟨2+codeWires k,context.common⟩]⟩,[⟨2+codeWires k,context⟩]⟩

/-- Entire common generation and mask record, not merely word equivalence.
No old context call occurs in the new runtime definition. -/
theorem plannedCandidateOccupationRun_common (k : ℕ) :
    (plannedCandidateOccupationRun k).common=maskedCandidateOccupationRun k := by
  simp only [plannedCandidateOccupationRun,booleanMaskContextProgram_common,maskedCandidateOccupationRun]

/-- Only the newly executed plan-table traces; common range/copy records are
already charged by common.accountedActions and are not counted twice. -/
def PlannedCandidateResult.planActions {n : ℕ} (r : PlannedCandidateResult n) : ℕ :=
  (r.contexts.map (fun p => p.2.planActions)).sum


theorem plannedCandidateOccupationRun_planActions (k : ℕ) :
    (plannedCandidateOccupationRun k).planActions≤1553*(k+3)^6 := by
  simp only [plannedCandidateOccupationRun,PlannedCandidateResult.planActions,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero]
  exact booleanMaskContextProgram_active_planActions k


def plannedCandidateStageRun (k : ℕ) : PlannedCandidateResult (originalWireCount (k+1)) :=
  let active:=plannedCandidateOccupationRun k
  ⟨⟨⟨prefixCode (active_available k) active.common.generation.word,active.common.generation.ranks,
    active.common.generation.stageTables⟩,active.common.masks⟩,active.contexts⟩


theorem plannedCandidateStageRun_common (k : ℕ) :
    (plannedCandidateStageRun k).common=maskedCandidateStageRun k := by
  simp only [plannedCandidateStageRun,plannedCandidateOccupationRun_common,maskedCandidateStageRun]


def plannedCandidateCompressionRun : (k : ℕ) → PlannedCandidateResult (originalWireCount k)
  | 0 => ⟨⟨⟨[],[],[]⟩,[]⟩,[]⟩
  | k+1 =>
    let previous:=plannedCandidateCompressionRun k
    let stage:=plannedCandidateStageRun k
    ⟨⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.common.generation.word)++stage.common.generation.word,
      previous.common.generation.ranks++stage.common.generation.ranks,
      previous.common.generation.stageTables++stage.common.generation.stageTables⟩,
      previous.common.masks++stage.common.masks⟩,previous.contexts++stage.contexts⟩


theorem plannedCandidateCompressionRun_common (k : ℕ) :
    (plannedCandidateCompressionRun k).common=maskedCandidateCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [plannedCandidateCompressionRun,maskedCandidateCompressionRun,plannedCandidateStageRun_common,ih]


theorem plannedCandidateCompressionRun_planActions (k : ℕ) :
    (plannedCandidateCompressionRun k).planActions≤1553*k*(k+3)^6 := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    have hs:=plannedCandidateOccupationRun_planActions k
    have hp:=Nat.pow_le_pow_left (show k+3≤k+1+3 by omega) 6
    have hi':=ih.trans (Nat.mul_le_mul_left (1553*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 1553 hp)
    change (((plannedCandidateCompressionRun k).contexts++(plannedCandidateStageRun k).contexts).map
      (fun p => p.2.planActions)).sum≤_
    rw [List.map_append,List.sum_append]
    exact (Nat.add_le_add hi' hs').trans_eq (by ring)

/-- Complete actual descriptor generator with direct Bool/list plan building
at every stage. No Finset/sort/minimum/erase Pauli-plan value path is used. -/
def plannedCandidateDescriptorRun (k : ℕ) : PlannedCandidateResult (originalWireCount k) :=
  let compression:=plannedCandidateCompressionRun k
  ⟨⟨⟨compression.common.generation.word++
      castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),
    compression.common.generation.ranks,compression.common.generation.stageTables⟩,compression.common.masks⟩,
    compression.contexts⟩


theorem plannedCandidateDescriptorRun_common (k : ℕ) :
    (plannedCandidateDescriptorRun k).common=maskedCandidateDescriptorRun k := by
  simp only [plannedCandidateDescriptorRun,plannedCandidateCompressionRun_common,maskedCandidateDescriptorRun]


theorem plannedCandidateDescriptorRun_word (k : ℕ) :
    (plannedCandidateDescriptorRun k).common.generation.word=extractionCode k := by
  rw [plannedCandidateDescriptorRun_common,maskedCandidateDescriptorRun_word]


theorem plannedCandidateDescriptorRun_planActions (k : ℕ) :
    (plannedCandidateDescriptorRun k).planActions≤1553*k*(k+3)^6 :=
  plannedCandidateCompressionRun_planActions k


def PlannedCandidateResult.accountedActions {n : ℕ} (r : PlannedCandidateResult n) : ℕ :=
  r.common.accountedActions+r.planActions


theorem plannedCandidateDescriptorRun_accountedActions (k : ℕ) :
    (plannedCandidateDescriptorRun k).accountedActions≤
      14098*k*(k+5)^9+1553*k*(k+3)^6 := by
  unfold PlannedCandidateResult.accountedActions
  rw [plannedCandidateDescriptorRun_common]
  exact Nat.add_le_add (maskedCandidateDescriptorRun_accountedActions_polynomial k)
    (plannedCandidateDescriptorRun_planActions k)


theorem plannedCandidateDescriptorRun_accountedActions_polynomial (k : ℕ) :
    (plannedCandidateDescriptorRun k).accountedActions≤15651*k*(k+5)^9 := by
  have hp : (k+3)^6≤(k+5)^9 := (Nat.pow_le_pow_left (show k+3≤k+5 by omega) 6).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  apply (plannedCandidateDescriptorRun_accountedActions k).trans
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left (1553*k) hp) _).trans_eq (by ring)

end EffectiveEncoding
