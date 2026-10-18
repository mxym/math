import EffectiveEncoding.FiniteLabelBitStream

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding


theorem compileAssembledWord_outputLength {m wires L q : ℕ}
    (synth : SingleCode → RetainedAssembledTargetResult m L q) (xs : WordCode wires) (B : ℕ)
    (hs : ∀ u,(synth u).cached.program.program.word.length≤B) :
    (compileAssembledWord synth xs).word.length≤xs.length*(B+1) := by
  induction xs with
  | nil => simp [compileAssembledWord]
  | cons g gs ih =>
    cases g with
    | single wire u =>
      have hu:=hs u
      simp only [compileAssembledWord,compileAssembledGate,List.length_append,wireLabels,List.length_map,
        List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    | cnot c t hct =>
      simp only [compileAssembledWord,compileAssembledGate,List.length_append,List.length_cons,List.length_nil,
        Nat.add_mul,Nat.one_mul]
      omega


def outputLabelBudget (k L p : ℕ) : ℕ :=
  actualGatePolynomial k*(32*L*(logarithmicPrecision k p+1)^5+1)


theorem fullyMaterializedInputRun_outputLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyMaterializedInputRun entry inverseLabel table L k p).compilation.value.word.length≤outputLabelBudget k L p := by
  let xs:=(scannedNativeDescriptorRun k).result.result.word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := by
    dsimp [xs]
    rw [scannedNativeDescriptorRun_result,binaryNativeDescriptorRun_result,
      preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (materializeWord (retainedAssembledTargetRun entry inverseLabel table L q) xs).value.word.length≤_
  rw [materializeWord_value]
  have h:=compileAssembledWord_outputLength _ xs (32*L*(q+1)^5)
    (retainedAssembledTargetRun_word_length entry inverseLabel table L q hL)
  apply h.trans
  rw [hq]
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (32*L) (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 5)) 1

structure SerializedInputResult (m wires L : ℕ) where
  execution : FullyMaterializedInputResult m wires L
  stream : BinaryStreamResult m wires

/-- The actual emitted finite-label word is encoded once as a Boolean stream.
No separate specification word or Nat-field list is substituted. -/
def serializedInputRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    SerializedInputResult m (originalWireCount k) L :=
  let execution:=fullyMaterializedInputRun entry inverseLabel table L k p
  let stream:=binaryLabelStream execution.compilation.value.word
  ⟨execution,stream⟩


def SerializedInputResult.decoded {m wires L : ℕ} (r : SerializedInputResult m wires L) : List (LabelGate m wires) :=
  deserializeLabelStream m wires r.stream.bits


theorem serializedInputRun_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (serializedInputRun entry inverseLabel table L k p).decoded=
      (fullyMaterializedInputRun entry inverseLabel table L k p).compilation.value.word :=
  deserializeLabelStream_roundtrip _


theorem serializedInputRun_suffix_roundtrip {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (tail : List Bool) :
    readBinaryLabelStream m (originalWireCount k)
      ((serializedInputRun entry inverseLabel table L k p).stream.bits++tail)=
      some ((fullyMaterializedInputRun entry inverseLabel table L k p).compilation.value.word,tail) :=
  readBinaryLabelStream_roundtrip _ tail


theorem serializedInputRun_bitLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (serializedInputRun entry inverseLabel table L k p).stream.bits.length≤
      outputLabelBudget k L p*(2*labelFieldWidth m (originalWireCount k)+2)+1 := by
  change (binaryLabelStream _).bits.length≤_
  rw [binaryLabelStream_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (fullyMaterializedInputRun_outputLength entry inverseLabel table L k p hL)) 1


theorem serializedInputRun_streamActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (serializedInputRun entry inverseLabel table L k p).stream.trace.actions≤
      outputLabelBudget k L p*(90*(labelFieldWidth m (originalWireCount k)+1)^2)+2 :=
  (binaryLabelStream_actions _).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _
    (fullyMaterializedInputRun_outputLength entry inverseLabel table L k p hL)) 2)


def SerializedInputResult.accountedPrimitiveActions {m wires L : ℕ} (r : SerializedInputResult m wires L) : ℕ :=
  r.execution.accountedPrimitiveActions+r.stream.trace.actions

/-- Fully explicit k,p bound, including only the specified retained primitive
models. No final cost/precision certificate is a premise of the bound. -/
def serializedPrimitiveBudget (m n L k p gateB : ℕ) : ℕ :=
  let Q:=logarithmicPrecision k p+1
  let N:=actualGatePolynomial k
  ((1800*k*(k+3)^8+(306*k*(k+4)^9+N*(200*(4*k+2)^2+
    nativeProviderCachePolynomialConstant L*(k+3)^15+actualInputOnlineCoefficient m n L k gateB)*Q^338))+
    N*((8192*(L+2*(n+1)+2))*Q^13))+(N*(12*(32*L*Q^5+2))+1)+
    (outputLabelBudget k L p*(90*(labelFieldWidth m (originalWireCount k)+1)^2)+2)


theorem serializedInputRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (serializedInputRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      serializedPrimitiveBudget m n L k p gateB :=
  Nat.add_le_add (fullyMaterializedInputRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he)
    (serializedInputRun_streamActions entry inverseLabel table L k p hL)

/-- Fidelity of the actual decoded Boolean stream, not just its pre-encoding
specification. Decoder correctness above discharges the value bridge. -/
theorem serializedInputRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (serializedInputRun entry inverseLabel table L k p).decoded))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [serializedInputRun_roundtrip]
  exact fullyMaterializedInputRun_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
