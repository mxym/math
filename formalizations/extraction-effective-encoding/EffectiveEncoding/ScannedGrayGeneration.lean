import EffectiveEncoding.ScannedOccupationCompilation

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev ScannedGrayRecord := Sigma ScannedGrayCompileResult

structure ScannedGrayCandidateResult (n : ℕ) where
  common : LetterSelectedCandidateResult n
  gray : List ScannedGrayRecord


def ScannedGrayCandidateResult.word {n : ℕ} (r : ScannedGrayCandidateResult n) : WordCode n :=
  r.common.common.common.generation.word


def scannedGrayOccupationRun (k : ℕ) : ScannedGrayCandidateResult (2+codeWires k) :=
  let context:=booleanMaskContextProgram (by omega : 0<2+codeWires k)
  let table:=acceptedOccupationTableProgram (k+1)
  let h:=acceptedOccupationTableProgram_sorted (k+1)
  let branches:=grayStoredLettersBranchTableRun context.common.plans table.items h
  let aligned:=grayStoredLettersAlignmentRun context.common.plans table.items h []
  ⟨⟨⟨⟨⟨branches.common.word++aligned.common.word,branches.common.ranks++aligned.common.ranks,
      [table.enumeration.common]⟩,[⟨2+codeWires k,context.common⟩]⟩,[⟨2+codeWires k,context⟩]⟩,[⟨k+1,table⟩]⟩,
    (branches.gray++aligned.gray).map (fun r => ⟨2+codeWires k,r⟩)⟩


theorem scannedGrayOccupationRun_common (k : ℕ) :
    (scannedGrayOccupationRun k).common=letterSelectedOccupationRun k := by
  simp only [scannedGrayOccupationRun,grayStoredLettersBranchTableRun_common,
    grayStoredLettersAlignmentRun_common,letterSelectedOccupationRun]

/-- Actual scan/projection/reverse records from this same packed compiler.
 No old Gray decision is executed to reconstruct an action counter. -/
def ScannedGrayCandidateResult.grayActions {n : ℕ} (r : ScannedGrayCandidateResult n) : ℕ :=
  (r.gray.map (fun p => p.2.actions)).sum


theorem scannedGrayOccupationRun_grayActions (k : ℕ) :
    (scannedGrayOccupationRun k).grayActions≤70*(k+2)^4+4*(scannedGrayOccupationRun k).word.length := by
  let context:=booleanMaskContextProgram (by omega : 0<2+codeWires k)
  let table:=acceptedOccupationTableProgram (k+1)
  let h:=acceptedOccupationTableProgram_sorted (k+1)
  have hb:=grayStoredLettersBranchTableRun_actions context.common.plans table.items h
  have ha:=grayStoredLettersAlignmentRun_actions context.common.plans table.items h []
  have hl : table.items.length≤(k+2)^3 := by
    have he:=congrArg List.length (acceptedOccupationTableProgram_native (k+1))
    simp only [List.length_map] at he
    change (acceptedOccupationTableProgram (k+1)).items.length≤_
    rw [he]
    exact candidateNativeTableProgram_length (k+1)
  have hn : 2+codeWires k≤2*(k+1) := by simpa only [originalWireCount_eq] using active_available k
  have hc : (5*(2+codeWires k)+4)*5≤70*(k+2) := by omega
  have hf : (5*(2+codeWires k)+4)*5*table.items.length≤70*(k+2)^4 :=
    (Nat.mul_le_mul hc hl).trans_eq (by ring)
  change ((((grayStoredLettersBranchTableRun context.common.plans table.items h).gray++
    (grayStoredLettersAlignmentRun context.common.plans table.items h []).gray).map
    (fun r => (⟨2+codeWires k,r⟩ : ScannedGrayRecord))).map
    (fun p => p.2.actions)).sum≤_
  simp only [List.map_map,Function.comp_def,List.map_append,List.sum_append]
  change (grayStoredLettersBranchTableRun context.common.plans table.items h).actions+
    (grayStoredLettersAlignmentRun context.common.plans table.items h []).actions≤70*(k+2)^4+4*((grayStoredLettersBranchTableRun context.common.plans table.items h).common.word++
    (grayStoredLettersAlignmentRun context.common.plans table.items h []).common.word).length
  unfold ScannedCandidateWordRun.actions at hb ha ⊢
  rw [List.length_append]
  have he : (5*(2+codeWires k)+4)*4*table.items.length+
      (5*(2+codeWires k)+4)*table.items.length=(5*(2+codeWires k)+4)*5*table.items.length := by ring
  omega


def scannedGrayStageRun (k : ℕ) : ScannedGrayCandidateResult (originalWireCount (k+1)) :=
  let active:=scannedGrayOccupationRun k
  ⟨⟨⟨⟨⟨prefixCode (active_available k) active.word,active.common.common.common.generation.ranks,
      active.common.common.common.generation.stageTables⟩,active.common.common.common.masks⟩,
      active.common.common.contexts⟩,active.common.tables⟩,active.gray⟩


theorem scannedGrayStageRun_common (k : ℕ) :
    (scannedGrayStageRun k).common=letterSelectedStageRun k := by
  simp only [scannedGrayStageRun,ScannedGrayCandidateResult.word,scannedGrayOccupationRun_common,letterSelectedStageRun]


def scannedGrayCompressionRun : (k : ℕ) → ScannedGrayCandidateResult (originalWireCount k)
  | 0 => ⟨⟨⟨⟨⟨[],[],[]⟩,[]⟩,[]⟩,[]⟩,[]⟩
  | k+1 =>
    let previous:=scannedGrayCompressionRun k
    let stage:=scannedGrayStageRun k
    ⟨⟨⟨⟨⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      previous.common.common.common.generation.ranks++stage.common.common.common.generation.ranks,
      previous.common.common.common.generation.stageTables++stage.common.common.common.generation.stageTables⟩,
      previous.common.common.common.masks++stage.common.common.common.masks⟩,
      previous.common.common.contexts++stage.common.common.contexts⟩,previous.common.tables++stage.common.tables⟩,
      previous.gray++stage.gray⟩


theorem scannedGrayCompressionRun_common (k : ℕ) :
    (scannedGrayCompressionRun k).common=letterSelectedCompressionRun k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scannedGrayCompressionRun,ScannedGrayCandidateResult.word,scannedGrayStageRun_common,
      letterSelectedCompressionRun,ih]


theorem scannedGrayCompressionRun_grayActions (k : ℕ) :
    (scannedGrayCompressionRun k).grayActions≤70*k*(k+2)^4+4*(scannedGrayCompressionRun k).word.length := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    have hs:=scannedGrayOccupationRun_grayActions k
    have hp:=Nat.pow_le_pow_left (show k+2≤k+1+2 by omega) 4
    have hi':=(Nat.add_le_add_right (Nat.mul_le_mul_left (70*k) hp)
      (4*(scannedGrayCompressionRun k).word.length))
    have hs':=Nat.add_le_add_right (Nat.mul_le_mul_left 70 hp) (4*(scannedGrayOccupationRun k).word.length)
    have ht:=Nat.add_le_add (ih.trans hi') (hs.trans hs')
    change (((scannedGrayCompressionRun k).gray++(scannedGrayStageRun k).gray).map (fun p => p.2.actions)).sum≤_
    rw [List.map_append,List.sum_append]
    change (scannedGrayCompressionRun k).grayActions+(scannedGrayOccupationRun k).grayActions≤_
    have hw : (scannedGrayCompressionRun (k+1)).word.length=
        (scannedGrayCompressionRun k).word.length+(scannedGrayStageRun k).word.length := by
      change ((show WordCode (originalWireCount (k+1)) from shiftCode 2 (scannedGrayCompressionRun k).word)++
        (scannedGrayStageRun k).word).length=_
      rw [List.length_append]
      exact congrArg (fun a => a+(scannedGrayStageRun k).word.length) (shiftCode_length 2 _)
    have hstage : (scannedGrayStageRun k).word.length=(scannedGrayOccupationRun k).word.length := by
      exact prefixCode_length _ _
    apply ht.trans_eq
    rw [hw,hstage]
    ring


def scannedGrayDescriptorRun (k : ℕ) : ScannedGrayCandidateResult (originalWireCount k) :=
  let compression:=scannedGrayCompressionRun k
  ⟨⟨⟨⟨⟨compression.word++
      castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),
    compression.common.common.common.generation.ranks,compression.common.common.common.generation.stageTables⟩,
    compression.common.common.common.masks⟩,compression.common.common.contexts⟩,compression.common.tables⟩,compression.gray⟩


theorem scannedGrayDescriptorRun_common (k : ℕ) :
    (scannedGrayDescriptorRun k).common=letterSelectedDescriptorRun k := by
  simp only [scannedGrayDescriptorRun,ScannedGrayCandidateResult.word,scannedGrayCompressionRun_common,
    letterSelectedDescriptorRun]


theorem scannedGrayDescriptorRun_word (k : ℕ) : (scannedGrayDescriptorRun k).word=extractionCode k := by
  unfold ScannedGrayCandidateResult.word
  rw [scannedGrayDescriptorRun_common,letterSelectedDescriptorRun_word]


theorem scannedGrayDescriptorRun_grayActions (k : ℕ) :
    (scannedGrayDescriptorRun k).grayActions≤70*k*(k+2)^4+4*(extractionCode k).length := by
  have h:=scannedGrayCompressionRun_grayActions k
  have hl : (scannedGrayCompressionRun k).word.length≤(extractionCode k).length := by
    rw [←scannedGrayDescriptorRun_word]
    dsimp only [scannedGrayDescriptorRun,ScannedGrayCandidateResult.word]
    simp only [List.length_append]
    omega
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hl) _)

end EffectiveEncoding
