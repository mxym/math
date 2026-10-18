import EffectiveEncoding.BooleanRankDescriptor
import EffectiveEncoding.FullyInputNativeExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure FullyScannedInputResult (m wires L : ℕ) where
  precision : ℕ
  generation : ScannedGeneratedRun wires
  compilation : InputCompiledLabelRun m wires L precision


def FullyScannedInputResult.erase {m wires L : ℕ} (r : FullyScannedInputResult m wires L) :
    FullyInputNativeResult m wires L :=
  ⟨r.precision,r.generation.result,r.compilation⟩

/-- The complete actual path uses native Boolean rank scans at every endpoint,
retained Boolean rank digits, actual native target providers and one retained
input-cache/numerical execution per single. -/
def fullyScannedInputRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyScannedInputResult m (originalWireCount k) L :=
  let generated:=scannedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.result.result.word.length (p+1)
  let compiled:=compileInputWord (retainedInputTargetRun entry inverseLabel table L q) generated.result.result.word
  ⟨q,generated,compiled⟩

/-- Entire prior execution record: generated word and actual digit records,
plus all retained provider/numerical/cache-read execution records. -/
theorem fullyScannedInputRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyScannedInputRun entry inverseLabel table L k p).erase=
      fullyInputNativeRun entry inverseLabel table L k p := by
  simp only [fullyScannedInputRun,FullyScannedInputResult.erase,scannedNativeDescriptorRun_result,fullyInputNativeRun]
  rw [scannedNativeDescriptorRun_result]


theorem fullyScannedInputRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyScannedInputRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  change (fullyScannedInputRun entry inverseLabel table L k p).erase.compilation.word=_
  rw [fullyScannedInputRun_erase,fullyInputNativeRun_word entry inverseLabel table L k p hL]


theorem fullyScannedInputRun_scanActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyScannedInputRun entry inverseLabel table L k p).generation.scanActions≤1800*k*(k+3)^8 :=
  scannedNativeDescriptorRun_scanActions k

/-- Add the actual retained count-word encoding/comparison traces to the same
input execution's rank-digit/provider/numeric/read charge. Other source costs
remain outside this explicit partial primitive model. -/
def FullyScannedInputResult.accountedPrimitiveActions {m wires L : ℕ} (r : FullyScannedInputResult m wires L) : ℕ :=
  r.generation.scanActions+r.erase.accountedPrimitiveActions


theorem fullyScannedInputRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyScannedInputRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      1800*k*(k+3)^8+(306*k*(k+4)^9+actualGatePolynomial k*(200*(4*k+2)^2+
        nativeProviderCachePolynomialConstant L*(k+3)^15+actualInputOnlineCoefficient m n L k gateB)*
          (logarithmicPrecision k p+1)^338) := by
  unfold FullyScannedInputResult.accountedPrimitiveActions
  apply Nat.add_le_add (fullyScannedInputRun_scanActions entry inverseLabel table L k p)
  rw [fullyScannedInputRun_erase]
  exact fullyInputNativeRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he


theorem fullyScannedInputRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyScannedInputRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyScannedInputRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
