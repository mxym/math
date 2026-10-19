import EffectiveEncoding.ScannedGrayGeneration

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure ScannedGraySerializedResult (m wires L : ℕ) where
  common : LetterSelectedSerializedResult m wires L
  gray : List ScannedGrayRecord

/-- The actual packed-scan compiler's generated word flows once to retained
 target/numeric/read/assembly compilation and actual Boolean serialization.
 Its same scan/projection/reverse records remain alongside all prior records. -/
def scannedGraySerializedRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : ScannedGraySerializedResult m (originalWireCount k) L :=
  let generated:=scannedGrayDescriptorRun k
  let precision:=dyadicCircuitPrecision generated.word.length (p+1)
  let compilation:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L precision) generated.word
  let stream:=binaryLabelStream compilation.value.word
  ⟨⟨⟨⟨⟨precision,generated.common.common.common.generation,compilation,stream⟩,
    generated.common.common.common.masks⟩,generated.common.common.contexts⟩,generated.common.tables⟩,generated.gray⟩


theorem scannedGraySerializedRun_common {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (scannedGraySerializedRun entry inverseLabel table L k p).common=
      letterSelectedSerializedRun entry inverseLabel table L k p := by
  simp only [scannedGraySerializedRun,ScannedGrayCandidateResult.word,scannedGrayDescriptorRun_common,
    letterSelectedSerializedRun]
  rw [scannedGrayDescriptorRun_common]


def ScannedGraySerializedResult.decoded {m wires L : ℕ} (r : ScannedGraySerializedResult m wires L) :
    List (LabelGate m wires) := r.common.decoded


theorem scannedGraySerializedRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((scannedGraySerializedRun entry inverseLabel table L k p).common.common.common.execution.stream.bits++tail)=
      some ((scannedGraySerializedRun entry inverseLabel table L k p).common.common.common.execution.compilation.value.word,tail) := by
  rw [scannedGraySerializedRun_common]
  exact letterSelectedSerializedRun_suffix_roundtrip entry inverseLabel table L k p tail


theorem scannedGraySerializedRun_decoded_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (scannedGraySerializedRun entry inverseLabel table L k p).decoded=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  unfold ScannedGraySerializedResult.decoded
  rw [scannedGraySerializedRun_common]
  exact letterSelectedSerializedRun_decoded_word entry inverseLabel table L k p hL


def ScannedGraySerializedResult.grayActions {m wires L : ℕ} (r : ScannedGraySerializedResult m wires L) : ℕ :=
  (r.gray.map (fun p => p.2.actions)).sum


theorem scannedGraySerializedRun_grayActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (scannedGraySerializedRun entry inverseLabel table L k p).grayActions≤
      70*k*(k+2)^4+4*(extractionCode k).length := scannedGrayDescriptorRun_grayActions k


theorem scannedGrayGeneration_uniform (k p : ℕ) :
    70*k*(k+2)^4+4*(extractionCode k).length≤
      4194374*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  generalize hbdef : k+3=b
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  have hfirst : 70*k*(k+2)^4≤70*b^24*Q^338 := by
    calc
      _≤70*b*b^4 := Nat.mul_le_mul (Nat.mul_le_mul_left 70 (by omega))
        (Nat.pow_le_pow_left (by omega : k+2≤b) 4)
      _=70*b^5 := by ring
      _≤_ := by
        simpa only [pow_zero,Nat.mul_one] using
          serializedMonomial_le b Q 70 5 0 24 338 hb hQ (by decide) (by decide)
  have hlen : (extractionCode k).length≤2^20*b^9 := by
    rw [←hbdef]
    exact (extractionCode_length_polynomial k).trans (actualGatePolynomial_power_bound k)
  have hlast : 4*(extractionCode k).length≤4194304*b^24*Q^338 := by
    calc
      _≤4*(2^20*b^9) := Nat.mul_le_mul_left 4 hlen
      _=4194304*b^9 := by norm_num <;> ring
      _≤_ := by
        simpa only [pow_zero,Nat.mul_one] using
          serializedMonomial_le b Q 4194304 9 0 24 338 hb hQ (by decide) (by decide)
  exact (Nat.add_le_add hfirst hlast).trans_eq (by ring)


def ScannedGraySerializedResult.accountedPrimitiveActions {m wires L : ℕ} (r : ScannedGraySerializedResult m wires L) : ℕ :=
  r.common.accountedPrimitiveActions+r.grayActions


def scannedGraySerializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  letterSelectedSerializedPolynomialConstant m n L gateB+4194374

/-- Only internally derived, same-execution local primitives are summed. The
 fixed-library queried-height contract remains explicit; the remaining host,
 move/update/index/AST/decoder/provider costs are not claimed included. -/
theorem scannedGraySerializedRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (scannedGraySerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      scannedGraySerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  unfold ScannedGraySerializedResult.accountedPrimitiveActions
  rw [scannedGraySerializedRun_common]
  have hp:=(scannedGraySerializedRun_grayActions entry inverseLabel table L k p).trans (scannedGrayGeneration_uniform k p)
  exact (Nat.add_le_add (letterSelectedSerializedRun_accountedPrimitiveActions_polynomial
    entry inverseLabel table L k p gateB hL he) hp).trans_eq (by
      unfold scannedGraySerializedPolynomialConstant
      rw [Nat.add_mul,Nat.add_mul])


theorem scannedGraySerializedRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (scannedGraySerializedRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [scannedGraySerializedRun_decoded_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
