import EffectiveEncoding.PackedSwapAlignment
import EffectiveEncoding.TripleRankExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Active-register alignment stores explicit Bool vectors. Branch generation
and Gray code retain their existing, separately costed representations. -/
def packedOccupationStepCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : WordCode (2+q) :=
  allBranchCode enc++(packedAlignmentRun (by omega) (pivotEmbedding enc) next (occupations (k+1)) []).word


theorem packedOccupationStepCode_eq {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    packedOccupationStepCode enc next=storedOccupationStepCode enc next := by
  simp only [packedOccupationStepCode,storedOccupationStepCode,packedAlignmentRun_word,
    packedStackBits,List.map_nil,storedSwapPermutation,storedAlignmentRun_empty_word]


def packedStageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k)
    (packedOccupationStepCode (tripleCompactEncoding k) (tripleNextEncoding k))


theorem packedStageCode_eq (k : ℕ) : packedStageCode k=tripleStoredStageCode k := by
  simp only [packedStageCode,tripleStoredStageCode,packedOccupationStepCode_eq]


def packedCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (packedCompressionCode k))++packedStageCode k


theorem packedCompressionCode_eq (k : ℕ) : packedCompressionCode k=tripleStoredCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [packedCompressionCode,tripleStoredCompressionCode,ih,packedStageCode_eq]


def packedExtractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  packedCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))


theorem packedExtractionCode_eq (k : ℕ) : packedExtractionCode k=tripleStoredExtractionCode k := by
  simp only [packedExtractionCode,tripleStoredExtractionCode,packedCompressionCode_eq]


def packedEndpointExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=packedExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem packedEndpointExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    packedEndpointExtractionCode entry inverseLabel table L k p=tripleRankExtractionCode entry inverseLabel table L k p := by
  simp only [packedEndpointExtractionCode,tripleRankExtractionCode,packedExtractionCode_eq]


theorem packedEndpointExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (packedEndpointExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [packedEndpointExtractionCode_eq]
  exact tripleRankExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz


def stagePackedEndpointCoordinates (k : ℕ) : ℕ :=
  (packedAlignmentRun (by omega) (pivotEmbedding (tripleCompactEncoding k)) (tripleNextEncoding k)
    (occupations (k+1)) []).endpointCoordinates


theorem stagePackedEndpointCoordinates_exact (k : ℕ) :
    stagePackedEndpointCoordinates k=2*activeWires k*occupationRank (k+1) := by
  have hn : 2+codeWires k=activeWires k := by unfold codeWires activeWires;omega
  simpa only [stagePackedEndpointCoordinates,packedAlignmentRun_coordinates,occupations_length,hn]


theorem stagePackedEndpointCoordinates_bound (k : ℕ) :
    stagePackedEndpointCoordinates k≤2*(6*Nat.clog 2 (k+3)+2)*(k+2)^3 := by
  rw [stagePackedEndpointCoordinates_exact]
  have hr : occupationRank (k+1)≤(k+2)^3 := by
    simpa only [occupations_length,Nat.add_assoc,Nat.reduceAdd] using enumeration_candidate_bound (k+1)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (activeWires_log_bound k)) hr


def extractionPackedEndpointCoordinates (k : ℕ) : ℕ :=
  ((List.range k).map stagePackedEndpointCoordinates).sum


theorem extractionPackedEndpointCoordinates_bound (k : ℕ) :
    extractionPackedEndpointCoordinates k≤k*(2*(6*Nat.clog 2 (k+3)+2)*(k+2)^3) := by
  unfold extractionPackedEndpointCoordinates
  calc
    _≤((List.range k).map (fun _ => 2*(6*Nat.clog 2 (k+3)+2)*(k+2)^3)).sum := by
      apply List.sum_le_sum
      intro j hj
      have hjk : j≤k := (List.mem_range.mp hj).le
      apply (stagePackedEndpointCoordinates_bound j).trans
      have hc:=Nat.clog_mono_right 2 (Nat.add_le_add_right hjk 3)
      gcongr
    _=_ := by simp

end EffectiveEncoding
