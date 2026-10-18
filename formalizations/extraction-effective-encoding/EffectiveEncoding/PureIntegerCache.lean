import EffectiveEncoding.PureIntegerProvider

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- An eagerly stored array of raw integer packets. -/
def buildRawPacketCache (f : ℕ → IntegerPacket) (P : ℕ) :
    List.Vector IntegerPacket (P+1) := List.Vector.ofFn (fun i => f i.val)

def readRawPacketCache {P : ℕ} (cache : List.Vector IntegerPacket (P+1)) (r : ℕ) :
    IntegerPacket := if h : r≤P then cache.get ⟨r,by omega⟩ else IntegerPacket.one

theorem rawPacketCache_value (f : ℕ → IntegerPacket) (P r : ℕ) :
    (readRawPacketCache (buildRawPacketCache f P) r).value=
      readPacketCache (buildPacketCache (fun q => (f q).value) P).1 r := by
  by_cases h : r≤P
  · simp [readRawPacketCache,buildRawPacketCache,readPacketCache,buildPacketCache,h]
  · simp only [readRawPacketCache,readPacketCache,h,dite_false]
    exact IntegerPacket.one_value r

theorem rawPacketCache_expression_value (f : ℕ → IntegerPacket) (P : ℕ) :
    evaluatePacketOracle (rawPacketExpressionOracle (readRawPacketCache (buildRawPacketCache f P)))=
      readPacketCache (buildPacketCache (fun q => (f q).value) P).1 := by
  rw [rawPacketExpressionOracle_eval]
  exact funext (rawPacketCache_value f P)

/-- Cache creation reads only raw packet fields. Online selection uses
integer cross-products and the binary division/square-root evaluator.
The AST embeds the fields as denominator-one literal data, never fractions. -/
def rawCachedIntegerRun {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (target : ℕ → IntegerPacket) : ArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildRawPacketCache (entry i) P)
  let targetCache:=buildRawPacketCache target P
  integerTracedPairWord (fun i => rawPacketExpressionOracle (readRawPacketCache (gates.get i)))
    inverseLabel table (Nat.clog 2 (q+1))
    (rawPacketExpressionOracle (readRawPacketCache targetCache))

/-- Only the output word is equated: the two programs deliberately retain
different expression trees and different raw denominator representations. -/
theorem rawCachedIntegerRun_word {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (target : ℕ → IntegerPacket) :
    (rawCachedIntegerRun entry inverseLabel table L q target).word=
      (cachedArithmeticRun (fun i r => (entry i r).value) inverseLabel table L q
        (fun r => (target r).value)).word := by
  rw [cachedArithmeticRun_word]
  simp only [rawCachedIntegerRun,integerTracedPairWord_eq,tracedPairWord_word,
    List.Vector.get_ofFn,rawPacketCache_expression_value,cachedNumericalRun]


def rawDescriptorRun {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : ArithmeticWordResult m :=
  rawCachedIntegerRun (fun i r => dyadicIntegerPacket (entry i) r) inverseLabel table L q u.rawPacket

theorem rawDescriptorRun_word {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) :
    (rawDescriptorRun entry inverseLabel table L q u).word=
      descriptorSynthesis (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L q u := by
  simp only [rawDescriptorRun,rawCachedIntegerRun_word,dyadicIntegerPacket_value,
    SingleCode.rawPacket_value,descriptorSynthesis]

end EffectiveEncoding
