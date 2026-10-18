import EffectiveEncoding.AssembledLabelCompilation

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure FullyAssembledInputResult (m wires L : ℕ) where
  precision : ℕ
  generation : ScannedGeneratedRun wires
  compilation : AssembledCompiledLabelRun m wires L precision


def FullyAssembledInputResult.erase {m wires L : ℕ} (r : FullyAssembledInputResult m wires L) :
    FullyScannedInputResult m wires L :=
  ⟨r.precision,r.generation,r.compilation.erase⟩

/-- Actual Boolean-scan generation, retained native target providers, online
numeric/cache reads and actual word/trace-list assembly in one retained run. -/
def fullyAssembledInputRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyAssembledInputResult m (originalWireCount k) L :=
  let generated:=scannedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.result.result.word.length (p+1)
  let compiled:=compileAssembledWord (retainedAssembledTargetRun entry inverseLabel table L q) generated.result.result.word
  ⟨q,generated,compiled⟩

/-- Full retained generation/provider/numeric/read execution record equality.
Only the additional actual assembly records are erased. -/
theorem fullyAssembledInputRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyAssembledInputRun entry inverseLabel table L k p).erase=
      fullyScannedInputRun entry inverseLabel table L k p := by
  simp only [fullyAssembledInputRun,FullyAssembledInputResult.erase,compileAssembledWord_erase,
    retainedAssembledTargetRun_erase,fullyScannedInputRun]


theorem fullyAssembledInputRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyAssembledInputRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  change (fullyAssembledInputRun entry inverseLabel table L k p).erase.compilation.word=_
  rw [fullyAssembledInputRun_erase,fullyScannedInputRun_word entry inverseLabel table L k p hL]


theorem fullyAssembledInputRun_assemblyActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyAssembledInputRun entry inverseLabel table L k p).compilation.assemblyActions≤
      actualGatePolynomial k*((8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13) := by
  let xs:=(scannedNativeDescriptorRun k).result.result.word
  let q:=dyadicCircuitPrecision xs.length (p+1)
  have hw : xs=extractionCode k := by
    dsimp [xs]
    rw [scannedNativeDescriptorRun_result,binaryNativeDescriptorRun_result,
      preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  have hq : q=extractionPrecision k p := by dsimp [q];rw [hw];rfl
  change (compileAssembledWord (retainedAssembledTargetRun entry inverseLabel table L q) xs).sumTrace
    RetainedAssembledTargetResult.assemblyActions≤_
  have h:=compileAssembledWord_sumTrace _ RetainedAssembledTargetResult.assemblyActions xs
    ((8192*(L+2*(n+1)+2))*(q+1)^13) (by
      intro wire u _
      exact retainedAssembledTargetRun_assemblyActions entry inverseLabel table L q hL u)
  apply h.trans
  rw [hq]
  apply Nat.mul_le_mul (by rw [hw];exact extractionCode_length_polynomial k)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 13)

/-- Count actual inverse-label provider invocations only; provider cost is not assigned. -/
theorem fullyAssembledInputRun_inverseCalls {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ)
    (hL : ∀ j,(table j).length≤L) :
    (fullyAssembledInputRun entry inverseLabel table L k p).compilation.inverseCalls≤
      actualGatePolynomial k*((8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13) :=
  (AssembledCompiledLabelRun.inverseCalls_le_assemblyActions _).trans
    (fullyAssembledInputRun_assemblyActions entry inverseLabel table L k p hL)

/-- Actual retained assembly trace plus the same execution's previously
accounted generation/preparation/provider/numerical/cache-read primitives. -/
def FullyAssembledInputResult.accountedPrimitiveActions {m wires L : ℕ}
    (r : FullyAssembledInputResult m wires L) : ℕ :=
  r.erase.accountedPrimitiveActions+r.compilation.assemblyActions


theorem fullyAssembledInputRun_accountedPrimitiveActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (fullyAssembledInputRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      (1800*k*(k+3)^8+(306*k*(k+4)^9+actualGatePolynomial k*(200*(4*k+2)^2+
        nativeProviderCachePolynomialConstant L*(k+3)^15+actualInputOnlineCoefficient m n L k gateB)*
          (logarithmicPrecision k p+1)^338))+
      actualGatePolynomial k*((8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13) := by
  unfold FullyAssembledInputResult.accountedPrimitiveActions
  apply Nat.add_le_add _ (fullyAssembledInputRun_assemblyActions entry inverseLabel table L k p hL)
  rw [fullyAssembledInputRun_erase]
  exact fullyScannedInputRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he


theorem fullyAssembledInputRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyAssembledInputRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyAssembledInputRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
