import EffectiveEncoding.NativeRankExtraction
import CircuitNumerical.WordSynthesisPolynomial

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Actual raw eager caches followed by the Boolean/list numerical evaluator.
The online result retains all executed expression/selection records. -/
def booleanRawCachedRun {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (target : ℕ → IntegerPacket) : WordArithmeticResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (entry i) P)
  let targetCache:=buildRawPacketCache target P
  wordTracedPairWord (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i)))
    inverseLabel table (Nat.clog 2 (q+1))
    (rawPacketExpressionOracle (readRawPacketCache targetCache))


theorem booleanRawCachedRun_result {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (target : ℕ → IntegerPacket) :
    (booleanRawCachedRun entry inverseLabel table L q target).result=
      (costedRawCachedRun entry inverseLabel table L q target).result := by
  simp only [booleanRawCachedRun,costedRawCachedRun,wordTracedPairWord_result,costedTracedPairWord_result]


theorem booleanRawCachedRun_actions_power {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    (target : ℕ → IntegerPacket) (a b C O : ℕ)
    (hbit : (booleanRawCachedRun entry inverseLabel table L q target).result.integerBitBudget≤C*(q+1)^a)
    (hops : (booleanRawCachedRun entry inverseLabel table L q target).result.operations≤O*(q+1)^b) :
    (booleanRawCachedRun entry inverseLabel table L q target).booleanActions≤
      40000*(2*C+4)^2*O*(q+1)^(2*a+b) :=
  wordTracedPairWord_booleanActions_power_bound _ _ _ _ _ q a b C O hbit hops


def booleanRawDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : WordArithmeticResult m :=
  booleanRawCachedRun (fun i r => dyadicIntegerPacket (entry i) r) inverseLabel table L q u.rawPacket


theorem booleanRawDescriptorRun_result {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (booleanRawDescriptorRun entry inverseLabel table L q u).result=
      (costedRawDescriptorRun entry inverseLabel table L q u).result :=
  booleanRawCachedRun_result _ _ _ _ _ _

structure BooleanProviderResult (m : ℕ) where
  online : WordArithmeticResult m
  providerRootCharge : ℕ

/-- Execute the actual target provider programs once per eager-cache precision,
retaining their raw integer values and root annotations. The online numerical
stage uses the Boolean/list backend; the provider's separate root annotation
is not added to the online Boolean action annotation. -/
def booleanTargetDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : BooleanProviderResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (fun r => dyadicIntegerPacket (entry i) r) P)
  let targetPrograms:=rawTargetProgramCache u P
  let targetCache:=targetPrograms.map PacketIntegerEvaluation.value
  let online:=wordTracedPairWord
    (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i))) inverseLabel table
    (Nat.clog 2 (q+1)) (rawPacketExpressionOracle (readRawPacketCache targetCache))
  ⟨online,∑ r : Fin (P+1),(targetPrograms.get r).rootCharge⟩


theorem booleanTargetDescriptorRun_online {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (booleanTargetDescriptorRun entry inverseLabel table L q u).online=
      booleanRawDescriptorRun entry inverseLabel table L q u := by
  simp only [booleanTargetDescriptorRun,rawTargetProgramCache_values,booleanRawDescriptorRun,booleanRawCachedRun]


theorem booleanTargetDescriptorRun_result {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (booleanTargetDescriptorRun entry inverseLabel table L q u).online.result=
      (targetProgramDescriptorRun entry inverseLabel table L q u).result := by
  rw [booleanTargetDescriptorRun_online,booleanRawDescriptorRun_result,targetProgramDescriptorRun_result,
    sharedRawDescriptorRun_eq]


theorem booleanTargetDescriptorRun_providerRootCharge {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (booleanTargetDescriptorRun entry inverseLabel table L q u).providerRootCharge=
      rawTargetProgramCacheCharge u L q := by
  simp only [booleanTargetDescriptorRun,rawTargetProgramCacheCharge,rawTargetProgramCache,List.Vector.get_ofFn]

end EffectiveEncoding
