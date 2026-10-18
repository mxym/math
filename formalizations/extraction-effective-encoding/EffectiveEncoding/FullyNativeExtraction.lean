import EffectiveEncoding.NativeLabelCompilation

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure FullyNativeExtractionResult (m wires L : ℕ) where
  precision : ℕ
  rankWork : RankWork
  compilation : NativeCompiledLabelRun m wires L precision

/-- Entire actual pipeline: native triple descriptor generation with shared
Pauli contexts; bounded Bool literal preparation once per SingleCode; native
half-angle/phase/packet provider; eager native input caches and Boolean numeric
synthesis; finite-label concatenation. Only semantic proofs use decoded data. -/
def fullyNativeExtractionRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : FullyNativeExtractionResult m (originalWireCount k) L :=
  let generated:=preparedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  let compiled:=compileNativeWord (nativeTargetDescriptorRun entry inverseLabel table L q) generated.word
  ⟨q,generated.work,compiled⟩


theorem fullyNativeExtractionRun_precision {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).precision=extractionPrecision k p := by
  simp only [fullyNativeExtractionRun,preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord,extractionPrecision]


theorem fullyNativeExtractionRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).compilation.word=
      numericalExtractionCode (fun i => nativePacketDataOracle (entry i)) inverseLabel table L k p := by
  simp only [fullyNativeExtractionRun,compileNativeWord_word,
    nativeTargetDescriptorRun_word entry inverseLabel table L _ hL,
    preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord,numericalExtractionCode]


theorem fullyNativeExtractionRun_preparationActions {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).compilation.preparationActions≤
      actualGatePolynomial k*(200*(4*k+2)^2) := by
  simp only [fullyNativeExtractionRun,preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  apply (compileNativeWord_preparationActions _ (extractionCode k) (200*(4*k+2)^2) (by
    intro wire u hu
    exact extractionCode_nativeInput_preparationActions hu)).trans
  exact Nat.mul_le_mul_right _ (extractionCode_length_polynomial k)


theorem fullyNativeExtractionRun_rankWork {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (i : Fin 3) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).rankWork i≤
      6*rankWorkConstant i*k*(k+2)^6 := by
  change (preparedNativeDescriptorRun k).work i≤_
  rw [preparedNativeDescriptorRun_eq]
  exact nativeDescriptorRun_work k i


theorem fullyNativeExtractionRun_programCount {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (fullyNativeExtractionRun entry inverseLabel table L k p).compilation.programs.length≤actualGatePolynomial k := by
  simp only [fullyNativeExtractionRun,preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord]
  exact (compileNativeWord_programs_length _ _).trans (extractionCode_length_polynomial k)


theorem fullyNativeExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → NativePacketDataOracle) (he : ∀ i,QApproximates (nativePacketDataOracle (entry i)) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (fullyNativeExtractionRun entry inverseLabel table L k p).compilation.word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [fullyNativeExtractionRun_word entry inverseLabel table L k p hL]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
