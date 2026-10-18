import EffectiveEncoding.PureIntegerBudgets
import CircuitNumerical.CostedNumericalProgram

open scoped Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Raw caches followed by explicit stored tuple coordinates/chart scores.
The returned charge counts binary-root routines only. -/
def costedRawCachedRun {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (target : ℕ → IntegerPacket) : CostedArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (entry i) P)
  let targetCache:=buildRawPacketCache target P
  costedTracedPairWord (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i)))
    inverseLabel table (Nat.clog 2 (q+1))
    (rawPacketExpressionOracle (readRawPacketCache targetCache))

theorem costedRawCachedRun_result {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (target : ℕ → IntegerPacket) :
    (costedRawCachedRun entry inverseLabel table L q target).result=
      rawCachedIntegerRun entry inverseLabel table L q target := by
  simp only [costedRawCachedRun,rawCachedIntegerRun,costedTracedPairWord_result,integerTracedPairWord_eq]

theorem costedRawCachedRun_rootCharge {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (target : ℕ → IntegerPacket) :
    (costedRawCachedRun entry inverseLabel table L q target).rootCharge≤
      (costedRawCachedRun entry inverseLabel table L q target).result.binaryRootPrimitiveOperations :=
  costedTracedPairWord_rootCharge _ _ _ _ _

def costedRawDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : CostedArithmeticWordResult m :=
  costedRawCachedRun (fun i r => dyadicIntegerPacket (entry i) r) inverseLabel table L q u.rawPacket

theorem costedRawDescriptorRun_result {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (costedRawDescriptorRun entry inverseLabel table L q u).result=
      rawDescriptorRun entry inverseLabel table L q u := costedRawCachedRun_result _ _ _ _ _ _

def costedRawExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  compileLabelWord (fun u => (costedRawDescriptorRun entry inverseLabel table L
    (extractionPrecision k p) u).result.word) (extractionCode k)

theorem costedRawExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    costedRawExtractionCode entry inverseLabel table L k p=rawExtractionCode entry inverseLabel table L k p := by
  simp only [costedRawExtractionCode,rawExtractionCode,costedRawDescriptorRun_result]

theorem costedRawExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (costedRawExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [costedRawExtractionCode_eq]
  exact rawExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

theorem costedRawDescriptorRun_integerBitBudget {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (costedRawDescriptorRun entry inverseLabel table L q u).result.integerBitBudget≤
      2*(actualTraceConstant n L*(k+3)^7*(q+1)^137) := by
  rw [costedRawDescriptorRun_result]
  exact rawDescriptorRun_polynomial entry G he inverseLabel table L q hL hu

/-- All binary division/sqrt internal natural operands represented by the
actual raw expression trace have a polynomial exponent, including temporaries. -/
theorem costedRawDescriptorRun_binaryProgramOperandTrace_height {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (x : ℕ) (hx : x∈(costedRawDescriptorRun entry inverseLabel table L q u).result.binaryProgramOperandTrace) :
    x≤2^(2*(2*(actualTraceConstant n L*(k+3)^7*(q+1)^137))+2) :=
  ArithmeticWordResult.binaryProgramOperandTrace_height _ _
    (costedRawDescriptorRun_integerBitBudget entry G he inverseLabel table L q hL hu) x hx

end EffectiveEncoding
