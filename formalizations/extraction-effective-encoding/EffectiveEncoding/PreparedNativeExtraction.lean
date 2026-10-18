import EffectiveEncoding.PreparedNativeGeneration

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The actual native/Boolean pipeline with one shared finite mask context per
stage. Word and the prior three distinct annotation models are preserved. -/
def preparedNativeBooleanExtractionRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : NativeBooleanResult m (originalWireCount k) :=
  let generated:=preparedNativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  let compiled:=booleanCompileWord (booleanTargetDescriptorRun entry inverseLabel table L q) generated.word
  ⟨compiled.word,generated.work,compiled.work⟩


theorem preparedNativeBooleanExtractionRun_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    preparedNativeBooleanExtractionRun entry inverseLabel table L k p=
      nativeBooleanExtractionRun entry inverseLabel table L k p := by
  simp only [preparedNativeBooleanExtractionRun,nativeBooleanExtractionRun,preparedNativeDescriptorRun_eq]


theorem preparedNativeBooleanExtractionRun_onlineActions {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (preparedNativeBooleanExtractionRun entry inverseLabel table L k p).numericWork 0≤
      actualGatePolynomial k*(actualBooleanDescriptorCoefficient n L k*(logarithmicPrecision k p+1)^338) := by
  rw [preparedNativeBooleanExtractionRun_eq]
  exact nativeBooleanExtractionRun_onlineActions entry G he inverseLabel table L k p hL


theorem preparedNativeBooleanExtractionRun_providerRootCharge {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (preparedNativeBooleanExtractionRun entry inverseLabel table L k p).numericWork 1≤
      actualGatePolynomial k*(rawProviderCachePolynomialConstant L*(k+3)^8*(logarithmicPrecision k p+1)^18) := by
  rw [preparedNativeBooleanExtractionRun_eq]
  exact nativeBooleanExtractionRun_providerRootCharge entry inverseLabel table L k p


theorem preparedNativeBooleanExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (preparedNativeBooleanExtractionRun entry inverseLabel table L k p).word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [preparedNativeBooleanExtractionRun_eq]
  exact nativeBooleanExtractionRun_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

/-- Total materialized context payload over the stages. This is a data-size
sum, not a runtime charge or a peak-space estimate. -/
def totalPreparedMaskPayload (k : ℕ) : ℕ :=
  ((List.range k).map (fun j => preparedMaskTablePayload
    (preparedMaskTable (by omega : 0<2+codeWires j)))).sum


theorem totalPreparedMaskPayload_bound (k : ℕ) : totalPreparedMaskPayload k≤k*(352*(k+3)^4) := by
  unfold totalPreparedMaskPayload
  calc
    _≤((List.range k).map (fun _ => 352*(k+3)^4)).sum := by
      apply List.sum_le_sum
      intro j hj
      exact (activePreparedMaskPayload j).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (Nat.add_le_add_right (List.mem_range.mp hj).le 3) 4))
    _=_ := by simp

end EffectiveEncoding
