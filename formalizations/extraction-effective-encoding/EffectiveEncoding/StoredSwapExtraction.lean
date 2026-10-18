import EffectiveEncoding.StoredSwapAlignment
import EffectiveEncoding.SharedRawCompiler

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The same stage compiler, with its alignment executed by an explicit
stored swap list rather than a composed permutation closure. -/
def storedOccupationStepCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : WordCode (2+q) :=
  allBranchCode enc++(storedAlignmentRun (by omega) (pivotEmbedding enc) next (occupations (k+1)) []).word

theorem storedOccupationStepCode_eq {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    storedOccupationStepCode enc next=occupationStepCode enc next := by
  simp only [storedOccupationStepCode,occupationStepCode,storedAlignmentRun_empty_word]


def storedStageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k) (storedOccupationStepCode (compactEncoding k) (nextEncoding k))

theorem storedStageCode_eq (k : ℕ) : storedStageCode k=stageCode k := by
  simp only [storedStageCode,stageCode,storedOccupationStepCode_eq]


def storedCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (storedCompressionCode k))++storedStageCode k

theorem storedCompressionCode_eq (k : ℕ) : storedCompressionCode k=compressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [storedCompressionCode,compressionCode,ih,storedStageCode_eq]


def storedExtractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  storedCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))

theorem storedExtractionCode_eq (k : ℕ) : storedExtractionCode k=extractionCode k := by
  simp only [storedExtractionCode,extractionCode,storedCompressionCode_eq]

/-- Materialize the new actual descriptor word once and derive its circuit
precision from that stored word's length. Numerical providers are the same
shared raw integer programs as in the independently frozen candidate. -/
def storedSharedRawExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=storedExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (sharedRawDescriptorRun entry inverseLabel table L q u).result.word) w

theorem storedSharedRawExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    storedSharedRawExtractionCode entry inverseLabel table L k p=
      sharedRawExtractionCode entry inverseLabel table L k p := by
  simp only [storedSharedRawExtractionCode,storedExtractionCode_eq,sharedRawExtractionCode,extractionPrecision]


theorem storedSharedRawExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (storedSharedRawExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [storedSharedRawExtractionCode_eq]
  exact sharedRawExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz


def stageStoredSwapApplications (k : ℕ) : ℕ :=
  (storedAlignmentRun (by omega) (pivotEmbedding (compactEncoding k)) (nextEncoding k)
    (occupations (k+1)) []).swapApplications


theorem stageStoredSwapApplications_exact (k : ℕ) :
    2*stageStoredSwapApplications k=occupationRank (k+1)*(occupationRank (k+1)-1) := by
  simpa only [stageStoredSwapApplications,List.length_nil,Nat.mul_zero,Nat.zero_add,occupations_length] using
    storedAlignmentRun_count (by omega) (pivotEmbedding (compactEncoding k)) (nextEncoding k)
      (occupations (k+1)) []


theorem stageStoredSwapApplications_bound (k : ℕ) : stageStoredSwapApplications k≤(k+2)^6 := by
  have hc:=storedAlignmentRun_empty_count_bound (by omega)
    (pivotEmbedding (compactEncoding k)) (nextEncoding k) (occupations (k+1))
  have hl : (occupations (k+1)).length≤(k+2)^3 := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using enumeration_candidate_bound (k+1)
  apply (hc.trans (Nat.pow_le_pow_left hl 2)).trans_eq
  rw [← pow_mul]


def extractionStoredSwapApplications (k : ℕ) : ℕ :=
  ((List.range k).map stageStoredSwapApplications).sum


theorem extractionStoredSwapApplications_bound (k : ℕ) :
    extractionStoredSwapApplications k≤k*(k+2)^6 := by
  unfold extractionStoredSwapApplications
  calc
    _≤((List.range k).map (fun _ => (k+2)^6)).sum := by
      apply List.sum_le_sum
      intro j hj
      apply (stageStoredSwapApplications_bound j).trans
      exact Nat.pow_le_pow_left (by have h:=List.mem_range.mp hj;omega) 6
    _=_ := by simp

end EffectiveEncoding
