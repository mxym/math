import EffectiveEncoding.PackedIndexedBranch
import EffectiveEncoding.RequestedPackedAlignment

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Store each branch result once; combine only its already built word and
its explicit embedding/mass request annotations. -/
def packedBranchTableRun {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    List (Sym (Fin 4) (k+1)) → PackedIndexedRun (2+q)
  | [] => ⟨[],0,0⟩
  | ν::νs =>
    let branch:=packedBranchRun enc ν
    let tail:=packedBranchTableRun enc νs
    ⟨branch.word++tail.word,branch.embeddingRequests+tail.embeddingRequests,branch.massRequests+tail.massRequests⟩


theorem packedBranchTableRun_word {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (xs : List (Sym (Fin 4) (k+1))) :
    (packedBranchTableRun enc xs).word=xs.flatMap (branchCode enc) := by
  induction xs with
  | nil => rfl
  | cons ν xs ih => simp only [packedBranchTableRun,List.flatMap_cons,packedBranchRun_word,ih]


theorem packedBranchTableRun_requests {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (xs : List (Sym (Fin 4) (k+1))) :
    (packedBranchTableRun enc xs).embeddingRequests≤4*xs.length ∧
      (packedBranchTableRun enc xs).massRequests≤4*xs.length := by
  induction xs with
  | nil => constructor <;> exact Nat.zero_le _
  | cons ν xs ih =>
    have h:=packedBranchRun_requests enc ν
    simp only [packedBranchTableRun,List.length_cons]
    constructor <;> omega


def directPackedOccupationRun {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : PackedIndexedRun (2+q) :=
  let occupationsHere:=(literalOccupationTable (k+1)).occupations
  let branches:=packedBranchTableRun enc occupationsHere
  let aligned:=requestedAlignmentRun (by omega) (pivotEmbedding enc) next occupationsHere []
  ⟨branches.word++aligned.result.word,branches.embeddingRequests+aligned.embeddingRequests,branches.massRequests⟩


theorem directPackedOccupationRun_word {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    (directPackedOccupationRun enc next).word=literalPackedOccupationStepCode enc next := by
  simp only [directPackedOccupationRun,literalPackedOccupationStepCode,packedBranchTableRun_word,
    requestedAlignmentRun_result]


theorem directPackedOccupationRun_requests {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    (directPackedOccupationRun enc next).embeddingRequests≤6*occupationRank (k+1) ∧
      (directPackedOccupationRun enc next).massRequests≤4*occupationRank (k+1) := by
  have hb:=packedBranchTableRun_requests enc (literalOccupationTable (k+1)).occupations
  have ha:=requestedAlignmentRun_requests (by omega) (pivotEmbedding enc) next
    (literalOccupationTable (k+1)).occupations []
  have hl : (literalOccupationTable (k+1)).occupations.length=occupationRank (k+1) := by
    rw [literalOccupationTable_value,builtOccupations_eq,occupations_length]
  simp only [directPackedOccupationRun]
  rw [hl] at hb ha
  constructor <;> omega


def directPackedStageRun (k : ℕ) : PackedIndexedRun (originalWireCount (k+1)) :=
  let active:=directPackedOccupationRun (constructedCompactEncoding k) (constructedNextEncoding k)
  ⟨prefixCode (active_available k) active.word,active.embeddingRequests,active.massRequests⟩


theorem directPackedStageRun_word (k : ℕ) : (directPackedStageRun k).word=literalStageCode k := by
  simp only [directPackedStageRun,literalStageCode,directPackedOccupationRun_word]


def directPackedCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (directPackedCompressionCode k))++(directPackedStageRun k).word


theorem directPackedCompressionCode_eq (k : ℕ) : directPackedCompressionCode k=literalCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [directPackedCompressionCode,literalCompressionCode,ih,directPackedStageRun_word]


def directPackedDescriptorCode (k : ℕ) : WordCode (originalWireCount k) :=
  directPackedCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))


theorem directPackedDescriptorCode_eq (k : ℕ) : directPackedDescriptorCode k=literalExtractionCode k := by
  simp only [directPackedDescriptorCode,literalExtractionCode,directPackedCompressionCode_eq]


def directPackedExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=directPackedDescriptorCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem directPackedExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    directPackedExtractionCode entry inverseLabel table L k p=literalOccupationExtractionCode entry inverseLabel table L k p := by
  simp only [directPackedExtractionCode,literalOccupationExtractionCode,directPackedDescriptorCode_eq]


theorem directPackedExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (directPackedExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [directPackedExtractionCode_eq]
  exact literalOccupationExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz


def extractionBranchEmbeddingRequests (k : ℕ) : ℕ :=
  ((List.range k).map (fun j => (directPackedStageRun j).embeddingRequests)).sum


theorem extractionBranchEmbeddingRequests_bound (k : ℕ) :
    extractionBranchEmbeddingRequests k≤k*(6*(k+2)^3) := by
  unfold extractionBranchEmbeddingRequests
  calc
    _≤((List.range k).map (fun _ => 6*(k+2)^3)).sum := by
      apply List.sum_le_sum
      intro j hj
      have hjk : j≤k := (List.mem_range.mp hj).le
      apply (directPackedOccupationRun_requests (constructedCompactEncoding j) (constructedNextEncoding j)).1.trans
      have hr : occupationRank (j+1)≤(j+2)^3 := by
        simpa only [occupations_length,Nat.add_assoc,Nat.reduceAdd] using enumeration_candidate_bound (j+1)
      exact Nat.mul_le_mul_left 6 (hr.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hjk 2) 3))
    _=_ := by simp

end EffectiveEncoding
