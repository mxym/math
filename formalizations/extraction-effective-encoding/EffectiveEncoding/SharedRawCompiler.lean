import EffectiveEncoding.ActualRawRootCharge
import CircuitNumerical.SharedCostedCompatibility

open scoped Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Stored raw input caches and stored root intermediates. The online root
annotation reuses the division already computed for the underlying value. -/
def sharedRawCachedRun {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (target : ℕ → IntegerPacket) : CostedArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (entry i) P)
  let targetCache:=buildRawPacketCache target P
  sharedCostedTracedPairWord (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i)))
    inverseLabel table (Nat.clog 2 (q+1))
    (rawPacketExpressionOracle (readRawPacketCache targetCache))

theorem sharedRawCachedRun_eq {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (target : ℕ → IntegerPacket) : sharedRawCachedRun entry inverseLabel table L q target=
      costedRawCachedRun entry inverseLabel table L q target := by
  simp only [sharedRawCachedRun,costedRawCachedRun,sharedCostedTracedPairWord_eq]


def sharedRawDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : CostedArithmeticWordResult m :=
  sharedRawCachedRun (fun i r => dyadicIntegerPacket (entry i) r) inverseLabel table L q u.rawPacket

theorem sharedRawDescriptorRun_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    sharedRawDescriptorRun entry inverseLabel table L q u=
      costedRawDescriptorRun entry inverseLabel table L q u := sharedRawCachedRun_eq _ _ _ _ _ _


def sharedRawExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  compileLabelWord (fun u => (sharedRawDescriptorRun entry inverseLabel table L
    (extractionPrecision k p) u).result.word) (extractionCode k)

theorem sharedRawExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    sharedRawExtractionCode entry inverseLabel table L k p=
      numericalExtractionCode (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L k p := by
  simp only [sharedRawExtractionCode,sharedRawDescriptorRun_eq,costedRawDescriptorRun_result,
    rawDescriptorRun_word,numericalExtractionCode,extractionPrecision]


theorem sharedRawExtractionCode_length {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576) (k p : ℕ) :
    (sharedRawExtractionCode entry inverseLabel table L k p).length≤
      (extractionCode k).length*(32*(L+1)*(extractionPrecision k p+1)^5) := by
  rw [sharedRawExtractionCode_eq]
  exact numericalExtractionCode_length G _ he inverseLabel hi table L hL hcover k p


theorem sharedRawExtractionCode_error {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576) (k p : ℕ) :
    ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-wordPhase (extractionCode k) •
        (denote (labelCircuit G (sharedRawExtractionCode entry inverseLabel table L k p)) :
          Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤(1/2:ℝ)^(p+1) := by
  rw [sharedRawExtractionCode_eq]
  exact numericalExtractionCode_error G _ he inverseLabel hi table L hL hcover k p


theorem sharedRawExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (sharedRawExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [sharedRawExtractionCode_eq]
  exact numericalExtractionCode_fidelity G _ he inverseLabel hi table L hL hcover k p z hz


theorem sharedRawDescriptorRun_rootCharge {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (sharedRawDescriptorRun entry inverseLabel table L q u).rootCharge≤actualRawRootCoefficient n L k*(q+1)^201 := by
  rw [sharedRawDescriptorRun_eq]
  exact costedRawDescriptorRun_rootCharge_polynomial entry G he inverseLabel table L q hL hu


theorem sharedRawDescriptorRun_integerBitBudget {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (sharedRawDescriptorRun entry inverseLabel table L (extractionPrecision k p) u).result.integerBitBudget≤
      rawLogarithmicOperandBudget n L k p := by
  rw [sharedRawDescriptorRun_eq,costedRawDescriptorRun_result]
  exact rawExtraction_integerBitBudget_logarithmic entry G he inverseLabel table L p hL hu


def gateSharedRawRootCharge {m n w : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) : GateCode w → ℕ
  | .single _ u => (sharedRawDescriptorRun entry inverseLabel table L q u).rootCharge
  | .cnot _ _ _ => 0

def extractionSharedRawRootCharge {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) : ℕ :=
  ((extractionCode k).map (gateSharedRawRootCharge entry inverseLabel table L (extractionPrecision k p))).sum


theorem extractionSharedRawRootCharge_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    extractionSharedRawRootCharge entry inverseLabel table L k p=extractionRawRootCharge entry inverseLabel table L k p := by
  have hg : gateSharedRawRootCharge (w:=originalWireCount k) entry inverseLabel table L (extractionPrecision k p)=
      gateRawRootCharge entry inverseLabel table L (extractionPrecision k p) := by
    funext g
    cases g <;> simp only [gateSharedRawRootCharge,gateRawRootCharge,sharedRawDescriptorRun_eq]
  simp only [extractionSharedRawRootCharge,extractionRawRootCharge,hg]


theorem extractionSharedRawRootCharge_bound {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionSharedRawRootCharge entry inverseLabel table L k p≤
      actualGatePolynomial k*(actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201) := by
  rw [extractionSharedRawRootCharge_eq]
  exact extractionRawRootCharge_polynomial entry G he inverseLabel table L k p hL

end EffectiveEncoding
