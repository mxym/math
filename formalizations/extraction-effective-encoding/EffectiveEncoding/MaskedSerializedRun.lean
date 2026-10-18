import EffectiveEncoding.MaskedCandidateGeneration
import EffectiveEncoding.CandidateSerializedPolynomial

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure MaskedSerializedResult (m wires L : ℕ) where
  execution : CandidateSerializedResult m wires L
  masks : List BinaryMaskRecord

/-- The terminal actually runs the new masked generator once and feeds its
same stored common generation record to materialization and serialization.
Old terminal calls do not appear in this runtime definition. -/
def maskedSerializedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : MaskedSerializedResult m (originalWireCount k) L :=
  let generated:=maskedCandidateDescriptorRun k
  let precision:=dyadicCircuitPrecision generated.generation.word.length (p+1)
  let compilation:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L precision) generated.generation.word
  let stream:=binaryLabelStream compilation.value.word
  ⟨⟨precision,generated.generation,compilation,stream⟩,generated.masks⟩

/-- Full common execution-record equality, including every target/provider/
numeric/read/assembly/output record. It follows from exact prepared-plan and
common-generation record equalities, not just from word equivalence. Actual
mask-generation records remain separately retained by the new terminal. -/
theorem maskedSerializedRun_execution {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (maskedSerializedRun entry inverseLabel table L k p).execution=
      candidateSerializedRun entry inverseLabel table L k p := by
  simp only [maskedSerializedRun,maskedCandidateDescriptorRun_generation,candidateSerializedRun]
  rw [maskedCandidateDescriptorRun_generation]


def MaskedSerializedResult.decoded {m wires L : ℕ} (r : MaskedSerializedResult m wires L) :
    List (LabelGate m wires) := r.execution.decoded


theorem maskedSerializedRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((maskedSerializedRun entry inverseLabel table L k p).execution.stream.bits++tail)=
      some ((maskedSerializedRun entry inverseLabel table L k p).execution.compilation.value.word,tail) := by
  rw [maskedSerializedRun_execution]
  exact candidateSerializedRun_suffix_roundtrip entry inverseLabel table L k p tail


theorem maskedSerializedRun_decoded_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (maskedSerializedRun entry inverseLabel table L k p).decoded=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  unfold MaskedSerializedResult.decoded
  rw [maskedSerializedRun_execution]
  exact candidateSerializedRun_decoded_word entry inverseLabel table L k p hL


def MaskedSerializedResult.maskActions {m wires L : ℕ} (r : MaskedSerializedResult m wires L) : ℕ :=
  (r.masks.map (fun p => p.2.actions)).sum


theorem maskedSerializedRun_maskActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (maskedSerializedRun entry inverseLabel table L k p).maskActions≤10592*k*(k+3)^6 :=
  maskedCandidateDescriptorRun_maskActions k


def MaskedSerializedResult.accountedPrimitiveActions {m wires L : ℕ} (r : MaskedSerializedResult m wires L) : ℕ :=
  r.execution.accountedPrimitiveActions+r.maskActions


theorem maskedGeneration_uniform (k p : ℕ) :
    10592*k*(k+3)^6≤10592*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  generalize hbdef : k+3=b
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  calc
    _≤10592*b*b^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _=10592*b^7 := by ring
    _≤_ := by
      simpa only [pow_zero,Nat.mul_one] using
        serializedMonomial_le b Q 10592 7 0 24 338 hb hQ (by decide) (by decide)


def maskedSerializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  candidateSerializedPolynomialConstant m n L gateB+10592

/-- The actual complete retained pipeline, now with its genuine binary mask
range/copy records. The contract is finite queried library height only; no
final-cost certificate is supplied, and the model is still explicitly partial. -/
theorem maskedSerializedRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (maskedSerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      maskedSerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  unfold MaskedSerializedResult.accountedPrimitiveActions
  rw [maskedSerializedRun_execution]
  have hm:=(maskedSerializedRun_maskActions entry inverseLabel table L k p).trans (maskedGeneration_uniform k p)
  exact (Nat.add_le_add (candidateSerializedRun_accountedPrimitiveActions_polynomial
    entry inverseLabel table L k p gateB hL he) hm).trans_eq (by
      unfold maskedSerializedPolynomialConstant
      rw [Nat.add_mul,Nat.add_mul])

/-- Original-register all-input fidelity of the actual decoded Boolean stream. -/
theorem maskedSerializedRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (maskedSerializedRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [maskedSerializedRun_decoded_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
