import EffectiveEncoding.InputLabelCompilation
import EffectiveEncoding.BinaryNativeExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Concrete trace projections from a single actual retained target execution. -/
def RetainedInputTargetResult.accountedActions {m L q : ℕ} (r : RetainedInputTargetResult m L q) : ℕ :=
  r.prepared.preparationActions+r.providerActions+r.cached.program.onlineActions


theorem retainedInputTargetRun_accountedActions {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (q+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(q+1)^9)) :
    (retainedInputTargetRun entry inverseLabel table L q u).accountedActions≤
      (200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
        actualInputOnlineCoefficient m n L k gateB)*(q+1)^338 := by
  have hp : (retainedInputTargetRun entry inverseLabel table L q u).prepared.preparationActions≤200*(4*k+2)^2 := by
    change (prepareNativeSingleInput u).preparationActions≤_
    rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord] at hu
    exact extractionCode_nativeInput_preparationActions hu
  have ht:=retainedInputTargetRun_providerActions_polynomial entry inverseLabel table L q hu
  have hn:=retainedInputTargetRun_onlineActions entry inverseLabel table L q gateB hL hu he
  have ha:=nativeAccountedPrimitive_algebra 1 (200*(4*k+2)^2)
    (nativeProviderCachePolynomialConstant L*(k+3)^15) (actualInputOnlineCoefficient m n L k gateB) (q+1) (by omega)
  simp only [Nat.one_mul] at ha
  exact (Nat.add_le_add (Nat.add_le_add hp ht) hn).trans ha

structure FullyInputNativeResult (m wires L : ℕ) where
  precision : ℕ
  generation : BinaryGeneratedRun wires
  compilation : InputCompiledLabelRun m wires L precision

/-- Actual descriptor generation and retained native target providers, followed
by the input-reference numeric/cache-read execution and finite-label output. -/
def fullyInputNativeRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyInputNativeResult m (originalWireCount k) L :=
  let generated:=binaryNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.result.word.length (p+1)
  let compiled:=compileInputWord (retainedInputTargetRun entry inverseLabel table L q) generated.result.word
  ⟨q,generated,compiled⟩


theorem fullyInputNativeRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyInputNativeRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  simp only [fullyInputNativeRun,compileInputWord_word,retainedInputTargetRun_word entry inverseLabel table L _ hL,
    binaryNativeDescriptorRun_result,preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord,numericalExtractionCode]


theorem fullyInputNativeRun_encodingActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyInputNativeRun entry inverseLabel table L k p).generation.encodingActions≤306*k*(k+4)^9 :=
  binaryNativeDescriptorRun_encodingActions k

/-- Same-execution model: actual generation rank digits, dynamic literal
preparation, target-provider numerical primitives, online numerical primitives
and all actually visited input-cache list reads. General source costs remain separate. -/
def FullyInputNativeResult.accountedPrimitiveActions {m wires L : ℕ} (r : FullyInputNativeResult m wires L) : ℕ :=
  r.generation.encodingActions+r.compilation.sumCharge RetainedInputTargetResult.accountedActions


theorem fullyInputNativeRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyInputNativeRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      306*k*(k+4)^9+actualGatePolynomial k*(200*(4*k+2)^2+
        nativeProviderCachePolynomialConstant L*(k+3)^15+actualInputOnlineCoefficient m n L k gateB)*
          (logarithmicPrecision k p+1)^338 := by
  have hg:=fullyInputNativeRun_encodingActions entry inverseLabel table L k p
  unfold FullyInputNativeResult.accountedPrimitiveActions
  apply Nat.add_le_add hg
  let xs:=(binaryNativeDescriptorRun k).result.word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hx : xs=(preparedNativeDescriptorRun k).word := by
    dsimp [xs];rw [binaryNativeDescriptorRun_result]
  have hw : xs=extractionCode k := by rw [hx,preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (compileInputWord (retainedInputTargetRun entry inverseLabel table L q) xs).sumCharge
    RetainedInputTargetResult.accountedActions≤_
  have h:=compileInputWord_sumCharge _ RetainedInputTargetResult.accountedActions xs
    ((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
      actualInputOnlineCoefficient m n L k gateB)*(q+1)^338) (by
        intro wire u hu
        apply retainedInputTargetRun_accountedActions entry inverseLabel table L q gateB hL
          (by rwa [←hx])
        simpa only [hq] using he)
  apply h.trans
  rw [hq]
  calc
    _≤actualGatePolynomial k*((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
      actualInputOnlineCoefficient m n L k gateB)*(logarithmicPrecision k p+1)^338) := by
      apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 338)
    _=_ := (Nat.mul_assoc _ _ _).symm


theorem fullyInputNativeRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyInputNativeRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyInputNativeRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
