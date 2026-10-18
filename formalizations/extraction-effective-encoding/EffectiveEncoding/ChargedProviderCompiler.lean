import EffectiveEncoding.RawProviderCacheBounds
import EffectiveEncoding.StoredSwapExtraction

open scoped BigOperators
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The target value and its provider-root annotation are stored together. -/
def rawTargetProgramCache (u : SingleCode) (P : ℕ) : List.Vector PacketIntegerEvaluation (P+1) :=
  List.Vector.ofFn (fun r => u.rawPacketProgram r.val)


theorem rawTargetProgramCache_values (u : SingleCode) (P : ℕ) :
    (rawTargetProgramCache u P).map PacketIntegerEvaluation.value=buildRawPacketCache u.rawPacket P := by
  apply List.Vector.ext
  intro r
  simp only [rawTargetProgramCache,buildRawPacketCache,List.Vector.get_map,List.Vector.get_ofFn,
    SingleCode.rawPacketProgram_value]

/-- Target-provider roots and online numerical roots, in one executable
stored result. Fixed dictionary evaluation and all nonroot costs are separate. -/
def targetProgramDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : CostedArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (fun r => dyadicIntegerPacket (entry i) r) P)
  let targetPrograms:=rawTargetProgramCache u P
  let targetCache:=targetPrograms.map PacketIntegerEvaluation.value
  let online:=sharedCostedTracedPairWord
    (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i))) inverseLabel table
    (Nat.clog 2 (q+1)) (rawPacketExpressionOracle (readRawPacketCache targetCache))
  ⟨online.result,(∑ r : Fin (P+1),(targetPrograms.get r).rootCharge)+online.rootCharge⟩


theorem targetProgramDescriptorRun_result {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (targetProgramDescriptorRun entry inverseLabel table L q u).result=
      (sharedRawDescriptorRun entry inverseLabel table L q u).result := by
  simp only [targetProgramDescriptorRun,rawTargetProgramCache_values,sharedRawDescriptorRun,sharedRawCachedRun]


theorem targetProgramDescriptorRun_rootCharge {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (targetProgramDescriptorRun entry inverseLabel table L q u).rootCharge=
      rawTargetProgramCacheCharge u L q+(sharedRawDescriptorRun entry inverseLabel table L q u).rootCharge := by
  simp only [targetProgramDescriptorRun,rawTargetProgramCache_values]
  simp only [sharedRawDescriptorRun,sharedRawCachedRun,rawTargetProgramCache,rawTargetProgramCacheCharge,List.Vector.get_ofFn]


theorem targetProgramDescriptorRun_rootCharge_bound {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (targetProgramDescriptorRun entry inverseLabel table L q u).rootCharge≤
      rawProviderCacheRootCoefficient k L*(q+1)^18+actualRawRootCoefficient n L k*(q+1)^201 := by
  rw [targetProgramDescriptorRun_rootCharge]
  exact Nat.add_le_add (rawTargetProgramCacheCharge_polynomial hu L q)
    (sharedRawDescriptorRun_rootCharge entry G he inverseLabel table L q hL hu)

/-- The stored-swap actual descriptor generator with both its target provider
and online numerical value program executed by shared raw integer roots. -/
def chargedProviderExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=storedExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem chargedProviderExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    chargedProviderExtractionCode entry inverseLabel table L k p=
      storedSharedRawExtractionCode entry inverseLabel table L k p := by
  simp only [chargedProviderExtractionCode,storedSharedRawExtractionCode,targetProgramDescriptorRun_result]


theorem chargedProviderExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (chargedProviderExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [chargedProviderExtractionCode_eq]
  exact storedSharedRawExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz


def gateProviderProgramRootCharge {m n w : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) : GateCode w → ℕ
  | .single _ u => (targetProgramDescriptorRun entry inverseLabel table L q u).rootCharge
  | .cnot _ _ _ => 0

def extractionProviderProgramRootCharge {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) : ℕ :=
  ((extractionCode k).map (gateProviderProgramRootCharge entry inverseLabel table L (extractionPrecision k p))).sum


theorem extractionProviderProgramRootCharge_bound {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionProviderProgramRootCharge entry inverseLabel table L k p≤actualGatePolynomial k*
      (rawProviderCacheRootCoefficient k L*(logarithmicPrecision k p+1)^18+
        actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201) := by
  unfold extractionProviderProgramRootCharge
  have hp:=extractionPrecision_logarithmic k p
  calc
    _≤((extractionCode k).map (fun _ =>
      rawProviderCacheRootCoefficient k L*(logarithmicPrecision k p+1)^18+
        actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201)).sum := by
      apply List.sum_le_sum
      intro g hg
      cases g with
      | single i u =>
        apply (targetProgramDescriptorRun_rootCharge_bound entry G he inverseLabel table L
          (extractionPrecision k p) hL hg).trans
        gcongr
      | cnot c t hct => exact Nat.zero_le _
    _=(extractionCode k).length*_
        := by simp
    _≤_ := Nat.mul_le_mul_right _ (extractionCode_length_polynomial k)

end EffectiveEncoding
