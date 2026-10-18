import EffectiveEncoding.NativeRankGeneration

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Compile the descriptor generated from native triples. The returned record
retains the rank annotations of that generation run. -/
def nativeRankExtractionRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : RankedLabelRun m (originalWireCount k) :=
  let generated:=nativeDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  ⟨compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word)
    generated.word,generated.work⟩


theorem nativeRankExtractionRun_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    nativeRankExtractionRun entry inverseLabel table L k p=rankedExtractionRun entry inverseLabel table L k p := by
  simp only [nativeRankExtractionRun,rankedExtractionRun,nativeDescriptorRun_eq]


theorem nativeRankExtractionRun_word {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (nativeRankExtractionRun entry inverseLabel table L k p).word=
      literalOccupationExtractionCode entry inverseLabel table L k p := by
  rw [nativeRankExtractionRun_eq]
  exact rankedExtractionRun_word entry inverseLabel table L k p


theorem nativeRankExtractionRun_work {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (i : Fin 3) :
    (nativeRankExtractionRun entry inverseLabel table L k p).rankWork i≤
      6*rankWorkConstant i*k*(k+2)^6 := by
  rw [nativeRankExtractionRun_eq]
  exact rankedExtractionRun_work entry inverseLabel table L k p i


theorem nativeRankExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (nativeRankExtractionRun entry inverseLabel table L k p).word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [nativeRankExtractionRun_eq]
  exact rankedExtractionRun_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
