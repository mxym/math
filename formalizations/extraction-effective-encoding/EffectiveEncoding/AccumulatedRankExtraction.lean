import EffectiveEncoding.AccumulatedRankGeneration

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure RankedLabelRun (m wires : ℕ) where
  word : List (LabelGate m wires)
  rankWork : RankWork

/-- The actual finite-label compiler consumes the stored generated descriptor
word and returns the rank annotations from that very generation run. Provider
and online arithmetic programs remain the charged raw integer programs. -/
def rankedExtractionRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : RankedLabelRun m (originalWireCount k) :=
  let generated:=rankedDescriptorRun k
  let q:=dyadicCircuitPrecision generated.word.length (p+1)
  ⟨compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word)
    generated.word,generated.work⟩


theorem rankedExtractionRun_word {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (rankedExtractionRun entry inverseLabel table L k p).word=
      literalOccupationExtractionCode entry inverseLabel table L k p := by
  simp only [rankedExtractionRun,literalOccupationExtractionCode,rankedDescriptorRun_word]


theorem rankedExtractionRun_work {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (i : Fin 3) :
    (rankedExtractionRun entry inverseLabel table L k p).rankWork i≤
      6*rankWorkConstant i*k*(k+2)^6 :=
  rankedDescriptorRun_work k i


theorem rankedExtractionRun_constructionSteps {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (rankedExtractionRun entry inverseLabel table L k p).rankWork 0≤168*k*(k+2)^6 :=
  rankedExtractionRun_work entry inverseLabel table L k p 0


theorem rankedExtractionRun_predicateQueries {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (rankedExtractionRun entry inverseLabel table L k p).rankWork 1≤6*k*(k+2)^6 :=
  rankedExtractionRun_work entry inverseLabel table L k p 1


theorem rankedExtractionRun_natEqualityQueries {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    (rankedExtractionRun entry inverseLabel table L k p).rankWork 2≤18*k*(k+2)^6 :=
  rankedExtractionRun_work entry inverseLabel table L k p 2


theorem rankedExtractionRun_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (rankedExtractionRun entry inverseLabel table L k p).word))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [rankedExtractionRun_word]
  exact literalOccupationExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
