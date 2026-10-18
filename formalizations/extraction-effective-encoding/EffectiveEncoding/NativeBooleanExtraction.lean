import EffectiveEncoding.BooleanLabelCompilation

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure NativeBooleanResult (m wires : ℕ) where
  word : List (LabelGate m wires)
  rankWork : RankWork
  numericWork : BooleanCompilationWork

/-- Native descriptor generation, actual stored provider caches, actual online
Boolean/list numeric evaluation, and stored finite-label concatenation. The
three source models remain distinct fields with their own specified meanings. -/
def nativeBooleanExtractionRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : NativeBooleanResult m (originalWireCount k) :=
  let generated:=nativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  let compiled:=booleanCompileWord (booleanTargetDescriptorRun entry inverseLabel table L q) generated.word
  ⟨compiled.word,generated.work,compiled.work⟩


theorem nativeBooleanExtractionRun_word {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (nativeBooleanExtractionRun entry inverseLabel table L k p).word=
      (nativeRankExtractionRun entry inverseLabel table L k p).word := by
  simp only [nativeBooleanExtractionRun,nativeRankExtractionRun,booleanCompileWord_word,
    booleanTargetDescriptorRun_result]


theorem nativeBooleanExtractionRun_rankWork {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (i : Fin 3) :
    (nativeBooleanExtractionRun entry inverseLabel table L k p).rankWork i≤
      6*rankWorkConstant i*k*(k+2)^6 := nativeDescriptorRun_work k i

/-- Actual online Boolean/list actions from the retained executed records.
Literal adapter, provider execution and structure are outside this field. -/
theorem nativeBooleanExtractionRun_onlineActions {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (nativeBooleanExtractionRun entry inverseLabel table L k p).numericWork 0≤
      actualGatePolynomial k*(actualBooleanDescriptorCoefficient n L k*(logarithmicPrecision k p+1)^338) := by
  simp only [nativeBooleanExtractionRun,nativeDescriptorRun_actualWord]
  change (booleanCompileWord (booleanTargetDescriptorRun entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k)).work 0≤_
  have h:=booleanCompileWord_work (booleanTargetDescriptorRun entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k) 0 (actualBooleanDescriptorCoefficient n L k*(extractionPrecision k p+1)^338) (by
      intro wire u hu
      exact booleanTargetDescriptorRun_actions entry G he inverseLabel table L (extractionPrecision k p) hL hu)
  apply h.trans
  apply Nat.mul_le_mul (extractionCode_length_polynomial k)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 338)

/-- Separate actual target-provider root annotation. It is not combined with
online Boolean actions or promoted to a whole-provider runtime bound. -/
theorem nativeBooleanExtractionRun_providerRootCharge {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (nativeBooleanExtractionRun entry inverseLabel table L k p).numericWork 1≤
      actualGatePolynomial k*(rawProviderCachePolynomialConstant L*(k+3)^8*(logarithmicPrecision k p+1)^18) := by
  simp only [nativeBooleanExtractionRun,nativeDescriptorRun_actualWord]
  change (booleanCompileWord (booleanTargetDescriptorRun entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k)).work 1≤_
  have h:=booleanCompileWord_work (booleanTargetDescriptorRun entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k) 1 (rawProviderCachePolynomialConstant L*(k+3)^8*(extractionPrecision k p+1)^18) (by
      intro wire u hu
      exact booleanTargetDescriptorRun_providerRootCharge_bound entry inverseLabel table L (extractionPrecision k p) hu)
  apply h.trans
  apply Nat.mul_le_mul (extractionCode_length_polynomial k)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (extractionPrecision_logarithmic k p) 1) 18)


theorem nativeBooleanExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (nativeBooleanExtractionRun entry inverseLabel table L k p).word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [nativeBooleanExtractionRun_word]
  exact nativeRankExtractionRun_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
