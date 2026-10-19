import EffectiveEncoding.CandidateWordPrograms
import EffectiveEncoding.BooleanRankDescriptor

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def candidateBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    List (NativeOccupation (k+1)) → CandidateWordRun (2+codeWires k)
  | [] => ⟨[],[]⟩
  | x::xs =>
    let branch:=candidateNativeBranchRun plans x
    let tail:=candidateBranchTableRun plans xs
    ⟨branch.word++tail.word,branch.ranks++tail.ranks⟩


theorem candidateBranchTableRun_word {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (candidateBranchTableRun plans xs).word=(scannedNativeBranchTableRun plans xs).result.result.word := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [candidateBranchTableRun,scannedNativeBranchTableRun,candidateNativeBranchRun_word,ih]


theorem candidateBranchTableRun_actions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (candidateBranchTableRun plans xs).actions≤2204*(k+5)^6*xs.length := by
  induction xs with
  | nil => exact le_refl 0
  | cons x xs ih =>
    change candidateRankRecordsActions ((candidateNativeBranchRun plans x).ranks++_)≤_
    rw [candidateRankRecordsActions_append]
    exact (Nat.add_le_add (candidateNativeBranchRun_actions plans x) ih).trans_eq
      (by simp only [List.length_cons];ring)

structure CandidateDescriptorResult (n : ℕ) where
  word : WordCode n
  ranks : List CandidateRankRecord
  stageTables : List BinaryTriplesResult


def CandidateDescriptorResult.actions {n : ℕ} (r : CandidateDescriptorResult n) : ℕ :=
  candidateRankRecordsActions r.ranks+(r.stageTables.map BinaryTriplesResult.actions).sum

/-- Stage table and every rank table use the actual stored-word generator.
Legacy rank-work fields are absent. These records are exactly the programs
whose values feed branch compilation and stored-swap alignment. -/
def candidateOccupationRun (k : ℕ) : CandidateDescriptorResult (2+codeWires k) :=
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let table:=candidateNativeTableProgram (k+1)
  let branches:=candidateBranchTableRun plans table.items
  let aligned:=candidateAlignmentRun plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []
  ⟨branches.word++aligned.word,branches.ranks++aligned.ranks,[table.enumeration]⟩


theorem candidateOccupationRun_word (k : ℕ) :
    (candidateOccupationRun k).word=(scannedNativeOccupationRun k).result.result.word := by
  have ha := candidateAlignmentRun_word (preparedMaskTable (by omega : 0<2+codeWires k))
    candidateNativePivotEndpoint candidateNativeNextEndpoint scannedNativePivotEndpoint scannedNativeNextEndpoint
    (candidateNativeTableProgram (k+1)).items [] candidateNativePivotEndpoint_point candidateNativeNextEndpoint_point
  rw [candidateNativeTableProgram_items] at ha
  simp only [candidateOccupationRun,candidateBranchTableRun_word,ha,candidateNativeTableProgram_items,
    scannedNativeOccupationRun]


theorem candidateOccupationRun_actions (k : ℕ) :
    (candidateOccupationRun k).actions≤3506*(k+5)^9 := by
  let plans:=preparedMaskTable (by omega : 0<2+codeWires k)
  let table:=candidateNativeTableProgram (k+1)
  have hb:=candidateBranchTableRun_actions plans table.items
  have ha:=candidateAlignmentRun_actions plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []
    (551*(k+5)^6) candidateNativePivotEndpoint_actions candidateNativeNextEndpoint_actions
  have hl : table.items.length≤(k+5)^3 :=
    (candidateNativeTableProgram_length (k+1)).trans (Nat.pow_le_pow_left (by omega) 3)
  have hrank : (candidateBranchTableRun plans table.items).actions+
      (candidateAlignmentRun plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []).actions≤3306*(k+5)^9 := by
    calc
      _≤2204*(k+5)^6*table.items.length+2*(551*(k+5)^6)*table.items.length := Nat.add_le_add hb ha
      _=3306*(k+5)^6*table.items.length := by ring
      _≤3306*(k+5)^6*(k+5)^3 := Nat.mul_le_mul_left _ hl
      _=_ := by ring
  have ht : table.enumeration.actions≤200*(k+5)^4 := by
    exact binaryTriplesProgram_actions_polynomial (k+1)
  have hp : (k+5)^4≤(k+5)^9 := Nat.pow_le_pow_right (by omega) (by decide)
  change candidateRankRecordsActions ((candidateBranchTableRun plans table.items).ranks++
    (candidateAlignmentRun plans candidateNativePivotEndpoint candidateNativeNextEndpoint table.items []).ranks)+
    ([table.enumeration].map BinaryTriplesResult.actions).sum≤_
  simp only [candidateRankRecordsActions_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact (Nat.add_le_add hrank (ht.trans (Nat.mul_le_mul_left 200 hp))).trans_eq (by ring)


def candidateStageRun (k : ℕ) : CandidateDescriptorResult (originalWireCount (k+1)) :=
  let active:=candidateOccupationRun k
  ⟨prefixCode (active_available k) active.word,active.ranks,active.stageTables⟩


theorem candidateStageRun_word (k : ℕ) :
    (candidateStageRun k).word=(scannedNativeStageRun k).result.result.word := by
  simp only [candidateStageRun,scannedNativeStageRun,candidateOccupationRun_word]


def candidateCompressionRun : (k : ℕ) → CandidateDescriptorResult (originalWireCount k)
  | 0 => ⟨[],[],[]⟩
  | k+1 =>
    let previous:=candidateCompressionRun k
    let stage:=candidateStageRun k
    ⟨(show WordCode (originalWireCount (k+1)) from shiftCode 2 previous.word)++stage.word,
      previous.ranks++stage.ranks,previous.stageTables++stage.stageTables⟩


theorem candidateCompressionRun_word (k : ℕ) :
    (candidateCompressionRun k).word=(scannedNativeCompressionRun k).result.result.word := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [candidateCompressionRun,scannedNativeCompressionRun,candidateStageRun_word,ih]


theorem candidateCompressionRun_actions (k : ℕ) :
    (candidateCompressionRun k).actions≤3506*k*(k+5)^9 := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
    have hs:=candidateOccupationRun_actions k
    have hp:=Nat.pow_le_pow_left (show k+5≤k+1+5 by omega) 9
    have hi':=ih.trans (Nat.mul_le_mul_left (3506*k) hp)
    have hs':=hs.trans (Nat.mul_le_mul_left 3506 hp)
    change candidateRankRecordsActions ((candidateCompressionRun k).ranks++(candidateStageRun k).ranks)+
      (((candidateCompressionRun k).stageTables++(candidateStageRun k).stageTables).map BinaryTriplesResult.actions).sum≤_
    rw [candidateRankRecordsActions_append,List.map_append,List.sum_append]
    have h : (candidateCompressionRun k).actions+(candidateStageRun k).actions≤3506*(k+1)*(k+1+5)^9 :=
      (Nat.add_le_add hi' hs').trans_eq (by ring)
    exact (by unfold CandidateDescriptorResult.actions at h;omega)

/-- Complete actual descriptor generation with binary candidate filters.
Bell/Gray/mask/prefix and remaining Nat/control construction are still ordinary
source programs and are explicitly outside the retained partial action model. -/
def candidateDescriptorRun (k : ℕ) : CandidateDescriptorResult (originalWireCount k) :=
  let compression:=candidateCompressionRun k
  ⟨compression.word++castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k))),
    compression.ranks,compression.stageTables⟩

/-- Literal complete word equality, not merely matrix equivalence. -/
theorem candidateDescriptorRun_word (k : ℕ) :
    (candidateDescriptorRun k).word=(scannedNativeDescriptorRun k).result.result.word := by
  simp only [candidateDescriptorRun,scannedNativeDescriptorRun,candidateCompressionRun_word]


theorem candidateDescriptorRun_extractionCode (k : ℕ) :
    (candidateDescriptorRun k).word=extractionCode k := by
  rw [candidateDescriptorRun_word,scannedNativeDescriptorRun_result,binaryNativeDescriptorRun_result,
    preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]


theorem candidateDescriptorRun_actions (k : ℕ) :
    (candidateDescriptorRun k).actions≤3506*k*(k+5)^9 := candidateCompressionRun_actions k

end EffectiveEncoding
