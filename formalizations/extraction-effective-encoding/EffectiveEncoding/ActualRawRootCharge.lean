import EffectiveEncoding.CostedRawCompiler
import EffectiveEncoding.LogarithmicPrecision
import CircuitNumerical.RawOperationGrowth

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

theorem costedRawCachedRun_operations {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (hL : ∀ j,(table j).length≤L) (target : ℕ → IntegerPacket) :
    (costedRawCachedRun entry inverseLabel table L q target).result.operations≤
      (1020*(n+1)*(2*L+1)*offsetGrowth)*(q+1)^64 := by
  simpa only [costedRawCachedRun,List.Vector.get_ofFn] using
    costedRawPacketPairWord_operations
      (fun i => readRawPacketCache (buildRawPacketCache (entry i) (numericalDemand L (Nat.clog 2 (q+1)))))
      inverseLabel table L q hL
      (readRawPacketCache (buildRawPacketCache target (numericalDemand L (Nat.clog 2 (q+1)))))

/-- This coefficient applies to the actual raw tuple AST, whose leaf
operation bound is 20, and uses the actual descriptor-derived integer height. -/
def actualRawRootCoefficient (n L k : ℕ) : ℕ :=
  (16*(2*(actualTraceConstant n L*(k+3)^7))+37)*(1020*(n+1)*(2*L+1)*offsetGrowth)

/-- A root-only annotation for underlying value evaluation. Provider cache
creation, other primitives and evaluation of the annotation itself are excluded. -/
theorem costedRawDescriptorRun_rootCharge_polynomial {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (costedRawDescriptorRun entry inverseLabel table L q u).rootCharge≤
      actualRawRootCoefficient n L k*(q+1)^201 := by
  let C:=2*(actualTraceConstant n L*(k+3)^7)
  let D:=1020*(n+1)*(2*L+1)*offsetGrowth
  let r:=costedRawDescriptorRun entry inverseLabel table L q u
  have hB : r.result.integerBitBudget≤C*(q+1)^137 := by
    simpa only [r,C,Nat.mul_assoc] using
      costedRawDescriptorRun_integerBitBudget entry G he inverseLabel table L q hL hu
  have hO : r.result.operations≤D*(q+1)^64 := costedRawCachedRun_operations _ _ _ L q hL _
  have hC : r.rootCharge≤r.result.binaryRootPrimitiveOperations := costedRawCachedRun_rootCharge _ _ _ _ _ _
  have h:=((hC.trans (ArithmeticWordResult.binaryRootPrimitiveOperations_bound r.result _ hB)).trans
    (Nat.mul_le_mul_left _ hO)).trans (cachedRootCost_algebra C D (q+1) (by omega))
  exact h


theorem costedRawDescriptorRun_rootCharge_logarithmic {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (costedRawDescriptorRun entry inverseLabel table L (extractionPrecision k p) u).rootCharge≤
      actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201 := by
  apply (costedRawDescriptorRun_rootCharge_polynomial entry G he inverseLabel table L
    (extractionPrecision k p) hL hu).trans
  gcongr
  exact extractionPrecision_logarithmic k p


def gateRawRootCharge {m n w : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) : GateCode w → ℕ
  | .single _ u => (costedRawDescriptorRun entry inverseLabel table L q u).rootCharge
  | .cnot _ _ _ => 0

def extractionRawRootCharge {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) : ℕ :=
  ((extractionCode k).map (gateRawRootCharge entry inverseLabel table L (extractionPrecision k p))).sum


theorem extractionRawRootCharge_bound {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionRawRootCharge entry inverseLabel table L k p≤
      (extractionCode k).length*(actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201) := by
  unfold extractionRawRootCharge
  calc
    _≤((extractionCode k).map (fun _ =>
      actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201)).sum := by
      apply List.sum_le_sum
      intro g hg
      cases g with
      | single i u => exact costedRawDescriptorRun_rootCharge_logarithmic entry G he inverseLabel table L p hL hg
      | cnot c t hct => exact Nat.zero_le _
    _=_ := by simp


theorem extractionRawRootCharge_polynomial {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionRawRootCharge entry inverseLabel table L k p≤
      actualGatePolynomial k*(actualRawRootCoefficient n L k*(logarithmicPrecision k p+1)^201) :=
  (extractionRawRootCharge_bound entry G he inverseLabel table L k p hL).trans
    (Nat.mul_le_mul_right _ (extractionCode_length_polynomial k))

end EffectiveEncoding
