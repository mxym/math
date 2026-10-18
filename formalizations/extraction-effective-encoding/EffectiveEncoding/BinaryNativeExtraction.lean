import EffectiveEncoding.BinaryDescriptorGeneration
import EffectiveEncoding.FullyRetainedNativeExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure BinaryNativeExtractionResult (m wires L : ℕ) where
  precision : ℕ
  generation : BinaryGeneratedRun wires
  compilation : ProviderCompiledLabelRun m wires L precision


def BinaryNativeExtractionResult.erase {m wires L : ℕ} (r : BinaryNativeExtractionResult m wires L) :
    FullyRetainedNativeResult m wires L :=
  ⟨r.precision,r.generation.result.work,r.compilation⟩

/-- Actual rank-digit construction now uses increment/trim and structural
copy/padding throughout the descriptor generator; all those execution records
are retained alongside the native provider and numerical execution records. -/
def binaryNativeExtractionRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : BinaryNativeExtractionResult m (originalWireCount k) L :=
  let generated:=binaryNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.result.word.length (p+1)
  let compiled:=compileProviderWord (retainedNativeTargetRun entry inverseLabel table L q) generated.result.word
  ⟨q,generated,compiled⟩


theorem binaryNativeExtractionRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (binaryNativeExtractionRun entry inverseLabel table L k p).erase=
      fullyRetainedNativeRun entry inverseLabel table L k p := by
  simp only [binaryNativeExtractionRun,BinaryNativeExtractionResult.erase,
    binaryNativeDescriptorRun_result,fullyRetainedNativeRun]
  rw [binaryNativeDescriptorRun_result]


theorem binaryNativeExtractionRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (binaryNativeExtractionRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  change (binaryNativeExtractionRun entry inverseLabel table L k p).erase.compilation.word=_
  rw [binaryNativeExtractionRun_erase,fullyRetainedNativeRun_word entry inverseLabel table L k p hL]


theorem binaryNativeExtractionRun_encodingActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (binaryNativeExtractionRun entry inverseLabel table L k p).generation.encodingActions≤306*k*(k+4)^9 :=
  binaryNativeDescriptorRun_encodingActions k

/-- Sum of precisely the retained rank-digit traces and previously accounted
preparation/provider/online numeric traces. Other source costs remain separate. -/
def BinaryNativeExtractionResult.accountedPrimitiveActions {m wires L : ℕ}
    (r : BinaryNativeExtractionResult m wires L) : ℕ :=
  r.generation.encodingActions+r.erase.accountedPrimitiveActions


theorem binaryNativeExtractionRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (binaryNativeExtractionRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      306*k*(k+4)^9+actualGatePolynomial k*(200*(4*k+2)^2+
        nativeProviderCachePolynomialConstant L*(k+3)^15+actualNativeBooleanCoefficient n L k gateB)*
          (logarithmicPrecision k p+1)^338 := by
  unfold BinaryNativeExtractionResult.accountedPrimitiveActions
  apply Nat.add_le_add (binaryNativeExtractionRun_encodingActions entry inverseLabel table L k p)
  rw [binaryNativeExtractionRun_erase]
  exact fullyRetainedNativeRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he


theorem binaryNativeExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (binaryNativeExtractionRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [binaryNativeExtractionRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
