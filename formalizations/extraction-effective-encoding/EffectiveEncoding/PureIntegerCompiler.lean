import EffectiveEncoding.PureIntegerCache

open scoped Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The actual finite-label compiler: actual integer descriptor packets,
raw integer eager caches, integer chart/base/stop selection, binary roots. -/
def rawExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  compileLabelWord (fun u => (rawDescriptorRun entry inverseLabel table L (extractionPrecision k p) u).word)
    (extractionCode k)

theorem rawExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    rawExtractionCode entry inverseLabel table L k p=
      numericalExtractionCode (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L k p := by
  simp only [rawExtractionCode,rawDescriptorRun_word,numericalExtractionCode,extractionPrecision]

theorem rawExtractionCode_uses {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    ∀ g∈labelCircuit G (rawExtractionCode entry inverseLabel table L k p),usesFiniteLibrary G g :=
  labelCircuit_uses G _

theorem rawExtractionCode_length {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576) (k p : ℕ) :
    (rawExtractionCode entry inverseLabel table L k p).length≤
      (extractionCode k).length*(32*(L+1)*(extractionPrecision k p+1)^5) := by
  rw [rawExtractionCode_eq]
  exact numericalExtractionCode_length G _ he inverseLabel hi table L hL hcover k p

theorem rawExtractionCode_error {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576) (k p : ℕ) :
    ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-wordPhase (extractionCode k) •
        (denote (labelCircuit G (rawExtractionCode entry inverseLabel table L k p)) :
          Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤(1/2:ℝ)^(p+1) := by
  rw [rawExtractionCode_eq]
  exact numericalExtractionCode_error G _ he inverseLabel hi table L hL hcover k p

theorem rawExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G (rawExtractionCode entry inverseLabel table L k p)))
        (pureMatrix (bitPurePower k z))).trace.re := by
  rw [rawExtractionCode_eq]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
