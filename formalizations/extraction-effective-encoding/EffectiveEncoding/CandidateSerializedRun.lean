import EffectiveEncoding.CandidateDescriptorGeneration
import EffectiveEncoding.SerializedPolynomialBudget

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure CandidateSerializedResult (m wires L : ℕ) where
  precision : ℕ
  generation : CandidateDescriptorResult wires
  compilation : MaterializedLabelRun m wires L precision
  stream : BinaryStreamResult m wires

/-- A single actual forward execution. The generated descriptor is retained
once; its same word selects precision and feeds materialization. Each target
run is retained by materializeWord and its same emitted labels feed the Boolean
encoder. No old generator is invoked to construct a compatibility record. -/
def candidateSerializedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : CandidateSerializedResult m (originalWireCount k) L :=
  let generation:=candidateDescriptorRun k
  let precision:=dyadicCircuitPrecision generation.word.length (p+1)
  let compilation:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L precision) generation.word
  let stream:=binaryLabelStream compilation.value.word
  ⟨precision,generation,compilation,stream⟩


def CandidateSerializedResult.decoded {m wires L : ℕ} (r : CandidateSerializedResult m wires L) :
    List (LabelGate m wires) := deserializeLabelStream m wires r.stream.bits


theorem candidateSerializedRun_generation {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (candidateSerializedRun entry inverseLabel table L k p).generation=candidateDescriptorRun k := rfl


theorem candidateSerializedRun_precision {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (candidateSerializedRun entry inverseLabel table L k p).precision=extractionPrecision k p := by
  simp only [candidateSerializedRun,candidateDescriptorRun_extractionCode,extractionPrecision]

/-- Exact gate list and arbitrary suffix from the actual emitted bitstream. -/
theorem candidateSerializedRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((candidateSerializedRun entry inverseLabel table L k p).stream.bits++tail)=
      some ((candidateSerializedRun entry inverseLabel table L k p).compilation.value.word,tail) :=
  readBinaryLabelStream_roundtrip _ tail


theorem candidateSerializedRun_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (candidateSerializedRun entry inverseLabel table L k p).decoded=
      (candidateSerializedRun entry inverseLabel table L k p).compilation.value.word :=
  deserializeLabelStream_roundtrip _

/-- Only value semantics is transported here. No old generation or whole
execution cost record is substituted into this actual terminal. -/
theorem candidateSerializedRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).compilation.value.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  simp only [candidateSerializedRun,candidateDescriptorRun_extractionCode,materializeWord_value]
  rw [candidateDescriptorRun_extractionCode]
  change (compileAssembledWord (retainedAssembledTargetRun entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k)).erase.word=_
  rw [compileAssembledWord_erase]
  simp only [retainedAssembledTargetRun_erase,compileInputWord_word,
    retainedInputTargetRun_word entry inverseLabel table L _ hL,numericalExtractionCode,extractionPrecision]


theorem candidateSerializedRun_decoded_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).decoded=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  rw [candidateSerializedRun_roundtrip,candidateSerializedRun_word entry inverseLabel table L k p hL]

/-- Original 2k-wire all-input fidelity of the genuinely decoded bitstream. -/
theorem candidateSerializedRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (candidateSerializedRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [candidateSerializedRun_decoded_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
