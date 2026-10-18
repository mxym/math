import EffectiveEncoding.RetainedProviderLabels

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure FullyRetainedNativeResult (m wires L : ℕ) where
  precision : ℕ
  rankWork : RankWork
  compilation : ProviderCompiledLabelRun m wires L precision


def FullyRetainedNativeResult.erase {m wires L : ℕ} (r : FullyRetainedNativeResult m wires L) :
    FullyNativeExtractionResult m wires L :=
  ⟨r.precision,r.rankWork,r.compilation.erase⟩

/-- Actual descriptor generation, literal preparation, retained target-provider
eager execution, native numerical synthesis and finite-label concatenation.
The runtime data path uses Word packets throughout. -/
def fullyRetainedNativeRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyRetainedNativeResult m (originalWireCount k) L :=
  let generated:=preparedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  let compiled:=compileProviderWord (retainedNativeTargetRun entry inverseLabel table L q) generated.word
  ⟨q,generated.work,compiled⟩

/-- Full record equality after erasing only the extra provider-execution records. -/
theorem fullyRetainedNativeRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).erase=
      fullyNativeExtractionRun entry inverseLabel table L k p := by
  simp only [fullyRetainedNativeRun,FullyRetainedNativeResult.erase,compileProviderWord_erase,
    retainedNativeTargetRun_erase,fullyNativeExtractionRun]


theorem fullyRetainedNativeRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  change (fullyRetainedNativeRun entry inverseLabel table L k p).erase.compilation.word=_
  rw [fullyRetainedNativeRun_erase,fullyNativeExtractionRun_word entry inverseLabel table L k p hL]

/-- All retained target-provider numeric primitive traces, summed over the
actual single-target executions. No provider is called by this projection. -/
theorem fullyRetainedNativeRun_providerActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).compilation.providerActions≤
      actualGatePolynomial k*(nativeProviderCachePolynomialConstant L*(k+3)^15*(logarithmicPrecision k p+1)^27) := by
  have hw : (preparedNativeDescriptorRun k).word=extractionCode k := by
    rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  let q:=dyadicCircuitPrecision (preparedNativeDescriptorRun k).word.length (p+1)
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (compileProviderWord (retainedNativeTargetRun entry inverseLabel table L q)
    (preparedNativeDescriptorRun k).word).providerActions≤_
  have h:=compileProviderWord_providerActions _ (preparedNativeDescriptorRun k).word
    (nativeProviderCacheCoefficient k L*(q+1)^27) (by
      intro wire u hu
      exact retainedNativeTargetRun_providerActions_polynomial entry inverseLabel table L q hu)
  apply h.trans
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  rw [hq]
  exact Nat.mul_le_mul (nativeProviderCacheCoefficient_polynomial k L)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 27)


theorem fullyRetainedNativeRun_preparationActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).compilation.erase.preparationActions≤
      actualGatePolynomial k*(200*(4*k+2)^2) := by
  change (fullyRetainedNativeRun entry inverseLabel table L k p).erase.compilation.preparationActions≤_
  rw [fullyRetainedNativeRun_erase]
  exact fullyNativeExtractionRun_preparationActions entry inverseLabel table L k p


theorem fullyRetainedNativeRun_numericalActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ)
    (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).compilation.erase.nativeActions≤
      actualGatePolynomial k*(actualNativeBooleanCoefficient n L k gateB*(logarithmicPrecision k p+1)^338) := by
  change (fullyRetainedNativeRun entry inverseLabel table L k p).erase.compilation.nativeActions≤_
  rw [fullyRetainedNativeRun_erase]
  exact fullyNativeExtractionRun_numericalActions entry inverseLabel table L k p gateB hL he

/-- Partial, specified primitive model only: dynamic input preparation,
all native target-provider numeric traces, and online numeric traces.
Library providers, syntax/list/cache/index/control/fuel/counter work remain separate. -/
def FullyRetainedNativeResult.accountedPrimitiveActions {m wires L : ℕ} (r : FullyRetainedNativeResult m wires L) : ℕ :=
  r.compilation.erase.preparationActions+r.compilation.providerActions+r.compilation.erase.nativeActions


theorem nativeAccountedPrimitive_algebra (N A T C x : ℕ) (hx : 1≤x) :
    N*A+N*(T*x^27)+N*(C*x^338)≤N*(A+T+C)*x^338 := by
  have h1 : 1≤x^338 := Nat.one_le_pow _ _ hx
  have h27 : x^27≤x^338 := Nat.pow_le_pow_right hx (by decide)
  have hA : N*A≤N*(A*x^338) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (Nat.mul_le_mul_left A h1)
  have hT:=Nat.mul_le_mul_left N (Nat.mul_le_mul_left T h27)
  apply (Nat.add_le_add_right (Nat.add_le_add hA hT) (N*(C*x^338))).trans_eq
  ring


theorem fullyRetainedNativeRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyRetainedNativeRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      actualGatePolynomial k*(200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
        actualNativeBooleanCoefficient n L k gateB)*(logarithmicPrecision k p+1)^338 := by
  have hp:=fullyRetainedNativeRun_preparationActions entry inverseLabel table L k p
  have ht:=fullyRetainedNativeRun_providerActions entry inverseLabel table L k p
  have hn:=fullyRetainedNativeRun_numericalActions entry inverseLabel table L k p gateB hL he
  exact (Nat.add_le_add (Nat.add_le_add hp ht) hn).trans
    (nativeAccountedPrimitive_algebra (actualGatePolynomial k) (200*(4*k+2)^2)
      (nativeProviderCachePolynomialConstant L*(k+3)^15)
      (actualNativeBooleanCoefficient n L k gateB) (logarithmicPrecision k p+1) (by omega))



theorem fullyRetainedNativeRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyRetainedNativeRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyRetainedNativeRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
