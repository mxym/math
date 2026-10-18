import EffectiveEncoding.MaterializedLabels

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding


theorem retainedAssembledTargetRun_word_length {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    (retainedAssembledTargetRun entry inverseLabel table L q u).cached.program.program.word.length≤32*L*(q+1)^5 := by
  rw [retainedAssembledTargetRun_cached,assembledInputCachedRun_program]
  exact inputCachedRun_length entry inverseLabel table L q hL _

structure FullyMaterializedInputResult (m wires L : ℕ) where
  precision : ℕ
  generation : ScannedGeneratedRun wires
  compilation : MaterializedLabelRun m wires L precision


def FullyMaterializedInputResult.erase {m wires L : ℕ} (r : FullyMaterializedInputResult m wires L) :
    FullyAssembledInputResult m wires L :=
  ⟨r.precision,r.generation,r.compilation.value⟩

/-- Actual outer label constructors, label-list copies and retained-program
list copies now return their concrete traces with the finite-label output. -/
def fullyMaterializedInputRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyMaterializedInputResult m (originalWireCount k) L :=
  let generated:=scannedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.result.result.word.length (p+1)
  let compiled:=materializeWord (retainedAssembledTargetRun entry inverseLabel table L q) generated.result.result.word
  ⟨q,generated,compiled⟩

/-- Entire retained run, including all provider/numeric/read/assembly data. -/
theorem fullyMaterializedInputRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyMaterializedInputRun entry inverseLabel table L k p).erase=
      fullyAssembledInputRun entry inverseLabel table L k p := by
  simp only [fullyMaterializedInputRun,FullyMaterializedInputResult.erase,materializeWord_value,fullyAssembledInputRun]


theorem fullyMaterializedInputRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyMaterializedInputRun entry inverseLabel table L k p).compilation.value.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  change (fullyMaterializedInputRun entry inverseLabel table L k p).erase.compilation.word=_
  rw [fullyMaterializedInputRun_erase,fullyAssembledInputRun_word entry inverseLabel table L k p hL]


theorem fullyMaterializedInputRun_outerActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyMaterializedInputRun entry inverseLabel table L k p).compilation.trace.actions≤
      actualGatePolynomial k*(12*(32*L*(logarithmicPrecision k p+1)^5+2))+1 := by
  let xs:=(scannedNativeDescriptorRun k).result.result.word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := by
    dsimp [xs]
    rw [scannedNativeDescriptorRun_result,binaryNativeDescriptorRun_result,
      preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
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

/-- Additional actual outer fixed-record/list traces. Existing Nat payloads
are referenced. This is not their bit-copy cost or whole source control cost. -/
def FullyMaterializedInputResult.accountedPrimitiveActions {m wires L : ℕ}
    (r : FullyMaterializedInputResult m wires L) : ℕ :=
  r.erase.accountedPrimitiveActions+r.compilation.trace.actions


theorem fullyMaterializedInputRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyMaterializedInputRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      ((1800*k*(k+3)^8+(306*k*(k+4)^9+actualGatePolynomial k*(200*(4*k+2)^2+
        nativeProviderCachePolynomialConstant L*(k+3)^15+actualInputOnlineCoefficient m n L k gateB)*
          (logarithmicPrecision k p+1)^338))+
      actualGatePolynomial k*((8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13))+
      (actualGatePolynomial k*(12*(32*L*(logarithmicPrecision k p+1)^5+2))+1) := by
  unfold FullyMaterializedInputResult.accountedPrimitiveActions
  apply Nat.add_le_add _ (fullyMaterializedInputRun_outerActions entry inverseLabel table L k p hL)
  rw [fullyMaterializedInputRun_erase]
  exact fullyAssembledInputRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he


theorem fullyMaterializedInputRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyMaterializedInputRun entry inverseLabel table L k p).compilation.value.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyMaterializedInputRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
