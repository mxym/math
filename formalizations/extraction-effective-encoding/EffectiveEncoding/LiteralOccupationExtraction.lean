import EffectiveEncoding.LiteralOccupations

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Store the constructed occupation records once and reuse their values in
both branch and packed-alignment traversal. -/
def literalPackedOccupationStepCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : WordCode (2+q) :=
  let occupationsHere:=(literalOccupationTable (k+1)).occupations
  occupationsHere.flatMap (branchCode enc)++
    (packedAlignmentRun (by omega) (pivotEmbedding enc) next occupationsHere []).word


theorem literalPackedOccupationStepCode_eq {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    literalPackedOccupationStepCode enc next=builtPackedOccupationStepCode enc next := by
  simp only [literalPackedOccupationStepCode,builtPackedOccupationStepCode,literalOccupationTable_value]


def literalStageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k)
    (literalPackedOccupationStepCode (constructedCompactEncoding k) (constructedNextEncoding k))


theorem literalStageCode_eq (k : ℕ) : literalStageCode k=constructedStageCode k := by
  simp only [literalStageCode,constructedStageCode,literalPackedOccupationStepCode_eq]


def literalCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (literalCompressionCode k))++literalStageCode k


theorem literalCompressionCode_eq (k : ℕ) : literalCompressionCode k=constructedCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [literalCompressionCode,constructedCompressionCode,ih,literalStageCode_eq]


def literalExtractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  literalCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))


theorem literalExtractionCode_eq (k : ℕ) : literalExtractionCode k=constructedExtractionCode k := by
  simp only [literalExtractionCode,constructedExtractionCode,literalCompressionCode_eq]


def literalOccupationExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=literalExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem literalOccupationExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    literalOccupationExtractionCode entry inverseLabel table L k p=constructiveRankExtractionCode entry inverseLabel table L k p := by
  simp only [literalOccupationExtractionCode,constructiveRankExtractionCode,literalExtractionCode_eq]


theorem literalOccupationExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (literalOccupationExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [literalOccupationExtractionCode_eq]
  exact constructiveRankExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz


def extractionOccupationLiteralSteps (k : ℕ) : ℕ :=
  ((List.range k).map (fun j => (literalOccupationTable (j+1)).literalSteps)).sum


theorem extractionOccupationLiteralSteps_bound (k : ℕ) :
    extractionOccupationLiteralSteps k≤k*((4*k+11)*(k+2)^3) := by
  unfold extractionOccupationLiteralSteps
  calc
    _≤((List.range k).map (fun _ => (4*k+11)*(k+2)^3)).sum := by
      apply List.sum_le_sum
      intro j hj
      have hjk : j≤k := (List.mem_range.mp hj).le
      have hjk' : j<k := List.mem_range.mp hj
      apply (literalOccupationTable_literalSteps (j+1)).trans
      simp only [Nat.add_assoc,Nat.reduceAdd]
      gcongr <;> omega
    _=_ := by simp


def extractionOccupationTripleSteps (k : ℕ) : ℕ :=
  ((List.range k).map (fun j => (literalOccupationTable (j+1)).tripleSteps)).sum


theorem extractionOccupationTripleSteps_bound (k : ℕ) :
    extractionOccupationTripleSteps k≤k*(28*(k+2)^3) := by
  unfold extractionOccupationTripleSteps
  calc
    _≤((List.range k).map (fun _ => 28*(k+2)^3)).sum := by
      apply List.sum_le_sum
      intro j hj
      have hjk : j≤k := (List.mem_range.mp hj).le
      have hjk' : j<k := List.mem_range.mp hj
      apply (literalOccupationTable_tripleSteps (j+1)).trans
      simp only [Nat.add_assoc,Nat.reduceAdd]
      gcongr <;> omega
    _=_ := by simp

end EffectiveEncoding
