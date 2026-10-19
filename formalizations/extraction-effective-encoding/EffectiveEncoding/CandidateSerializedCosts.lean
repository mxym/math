import EffectiveEncoding.CandidateSerializedRun

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Direct projections of this same retained preparation/provider/input-numeric/
cache-read/assembly record. Summing these annotations is not itself charged. -/
def RetainedAssembledTargetResult.primitiveActions {m L q : ℕ}
    (r : RetainedAssembledTargetResult m L q) : ℕ :=
  r.prepared.preparationActions+
    (r.providerPrograms.toList.map (fun run => run.trace.booleanActions)).sum+
    r.cached.program.program.onlineActions+r.cached.program.trace.actions

/-- This compatibility is a projection of the very same target record. It
neither invokes an old descriptor generator nor substitutes a word-only cost. -/
theorem RetainedAssembledTargetResult.primitiveActions_eq {m L q : ℕ}
    (r : RetainedAssembledTargetResult m L q) :
    r.primitiveActions=r.erase.accountedActions+r.assemblyActions := rfl


theorem retainedAssembledTargetRun_primitiveActions {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (q+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(q+1)^9)) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).primitiveActions≤
      (200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
        actualInputOnlineCoefficient m n L k gateB)*(q+1)^338+
      (8192*(L+2*(n+1)+2))*(q+1)^13 := by
  rw [RetainedAssembledTargetResult.primitiveActions_eq,retainedAssembledTargetRun_erase]
  exact Nat.add_le_add (retainedInputTargetRun_accountedActions entry inverseLabel table L q gateB hL hu he)
    (retainedAssembledTargetRun_assemblyActions entry inverseLabel table L q hL u)


def CandidateSerializedResult.targetActions {m wires L : ℕ} (r : CandidateSerializedResult m wires L) : ℕ :=
  r.compilation.value.sumTrace RetainedAssembledTargetResult.primitiveActions


theorem candidateSerializedRun_targetActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (candidateSerializedRun entry inverseLabel table L k p).targetActions≤
      actualGatePolynomial k*((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
        actualInputOnlineCoefficient m n L k gateB)*(logarithmicPrecision k p+1)^338+
        (8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13) := by
  let xs:=(candidateDescriptorRun k).word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := candidateDescriptorRun_extractionCode k
  have hx : xs=(preparedNativeDescriptorRun k).word := by rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord];exact hw
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (materializeWord (retainedAssembledTargetRun entry inverseLabel table L q) xs).value.sumTrace
    RetainedAssembledTargetResult.primitiveActions≤_
  rw [materializeWord_value]
  have h:=compileAssembledWord_sumTrace _ RetainedAssembledTargetResult.primitiveActions xs
    ((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
      actualInputOnlineCoefficient m n L k gateB)*(q+1)^338+(8192*(L+2*(n+1)+2))*(q+1)^13) (by
      intro wire u hu
      apply retainedAssembledTargetRun_primitiveActions entry inverseLabel table L q gateB hL
        (by rwa [←hx])
      simpa only [hq] using he)
  apply h.trans
  rw [hq]
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 338)
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 13)


theorem candidateSerializedRun_outputLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).compilation.value.word.length≤outputLabelBudget k L p := by
  let xs:=(candidateDescriptorRun k).word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := candidateDescriptorRun_extractionCode k
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (materializeWord (retainedAssembledTargetRun entry inverseLabel table L q) xs).value.word.length≤_
  rw [materializeWord_value]
  have h:=compileAssembledWord_outputLength _ xs (32*L*(q+1)^5)
    (retainedAssembledTargetRun_word_length entry inverseLabel table L q hL)
  apply h.trans
  rw [hq]
  unfold outputLabelBudget
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (32*L) (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 5)) 1


theorem candidateSerializedRun_outerActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).compilation.trace.actions≤
      actualGatePolynomial k*(12*(32*L*(logarithmicPrecision k p+1)^5+2))+1 := by
  let xs:=(candidateDescriptorRun k).word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := candidateDescriptorRun_extractionCode k
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (materializeWord (retainedAssembledTargetRun entry inverseLabel table L q) xs).trace.actions≤_
  have h:=materializeWord_actions _ xs (32*L*(q+1)^5) (by
    intro wire u _
    exact retainedAssembledTargetRun_word_length entry inverseLabel table L q hL u)
  apply h.trans
  rw [hq]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  exact Nat.mul_le_mul_left 12 (Nat.add_le_add_right
    (Nat.mul_le_mul_left (32*L) (Nat.pow_le_pow_left
      (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 5)) 2)


theorem candidateSerializedRun_streamLength {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).stream.bits.length≤
      outputLabelBudget k L p*(2*labelFieldWidth m (originalWireCount k)+2)+1 := by
  change (binaryLabelStream _).bits.length≤_
  rw [binaryLabelStream_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (candidateSerializedRun_outputLength entry inverseLabel table L k p hL)) 1


theorem candidateSerializedRun_streamActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (candidateSerializedRun entry inverseLabel table L k p).stream.trace.actions≤
      outputLabelBudget k L p*(90*(labelFieldWidth m (originalWireCount k)+1)^2)+2 := by
  change (binaryLabelStream _).trace.actions≤_
  exact (binaryLabelStream_actions _).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _
    (candidateSerializedRun_outputLength entry inverseLabel table L k p hL)) 2)

/-- Exactly the retained actual generation and per-target preparation/provider/
numeric/read/assembly records, outer materialization and output encoding. No
old whole-execution cost record appears in this definition. -/
def CandidateSerializedResult.accountedPrimitiveActions {m wires L : ℕ}
    (r : CandidateSerializedResult m wires L) : ℕ :=
  r.generation.actions+r.targetActions+r.compilation.trace.actions+r.stream.trace.actions

/-- Fully explicit numeric envelope for the specified partial models only. -/
def candidateSerializedPrimitiveBudget (m n L k p gateB : ℕ) : ℕ :=
  let Q:=logarithmicPrecision k p+1
  let N:=actualGatePolynomial k
  3506*k*(k+5)^9+
    N*((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
      actualInputOnlineCoefficient m n L k gateB)*Q^338+(8192*(L+2*(n+1)+2))*Q^13)+
    (N*(12*(32*L*Q^5+2))+1)+
    (outputLabelBudget k L p*(90*(labelFieldWidth m (originalWireCount k)+1)^2)+2)


theorem candidateSerializedRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (candidateSerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      candidateSerializedPrimitiveBudget m n L k p gateB :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (candidateDescriptorRun_actions k)
    (candidateSerializedRun_targetActions entry inverseLabel table L k p gateB hL he))
    (candidateSerializedRun_outerActions entry inverseLabel table L k p hL))
    (candidateSerializedRun_streamActions entry inverseLabel table L k p hL)

end EffectiveEncoding
