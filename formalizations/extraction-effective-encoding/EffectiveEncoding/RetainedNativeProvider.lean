import EffectiveEncoding.NativeProviderBooleanBudgets
import EffectiveEncoding.ActualNativeNumericalBudget

open scoped BigOperators
open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The actual eager evaluations, materialized once before the numerical run. -/
def buildNativeTargetPrograms (u : NativeSingleInput) (P : ℕ) :
    List.Vector PacketWordEvaluation (P+1) :=
  List.Vector.ofFn (fun r => u.packetProgram r.val)


theorem buildNativeTargetPrograms_values (u : NativeSingleInput) (P : ℕ) :
    (buildNativeTargetPrograms u P).map PacketWordEvaluation.value=buildNativePacketCache u.packetDataOracle P := by
  apply List.Vector.ext
  intro i
  simp only [buildNativeTargetPrograms,buildNativePacketCache,List.Vector.get_map,List.Vector.get_ofFn,
    NativeSingleInput.packetDataOracle]

structure RetainedNativeTargetResult (m L q : ℕ) where
  prepared : NativeSingleInput
  providerPrograms : List.Vector PacketWordEvaluation (numericalDemand L (Nat.clog 2 (q+1))+1)
  cached : NativeCachedWordResult m (numericalDemand L (Nat.clog 2 (q+1)))

/-- The target provider is executed once per eager-cache request. Its value
and trace remain in the same retained record. The numerical recursion reads
only the stored Word packet values. No decode/Rat/Nat.bits path is executed. -/
def retainedNativeTargetRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : RetainedNativeTargetResult m L q :=
  let prepared:=prepareNativeSingleInput u
  let depth:=Nat.clog 2 (q+1)
  let P:=numericalDemand L depth
  let gateCaches:=List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) P)
  let targetPrograms:=buildNativeTargetPrograms prepared P
  let targetCache:=targetPrograms.map PacketWordEvaluation.value
  let program:=nativeTracedPairWord (fun i => nativeCachedPacketOracle (gateCaches.get i))
    inverseLabel table depth (nativeCachedPacketOracle targetCache)
  ⟨prepared,targetPrograms,⟨gateCaches,targetCache,program⟩⟩


def RetainedNativeTargetResult.erase {m L q : ℕ} (r : RetainedNativeTargetResult m L q) : NativeTargetResult m L q :=
  ⟨r.prepared,r.cached⟩

/-- Entire previous target execution record, not only its output semantics. -/
theorem retainedNativeTargetRun_erase {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedNativeTargetRun entry inverseLabel table L q u).erase=
      nativeTargetDescriptorRun entry inverseLabel table L q u := by
  simp only [retainedNativeTargetRun,RetainedNativeTargetResult.erase,buildNativeTargetPrograms_values,
    nativeTargetDescriptorRun,nativeCachedRun]

/-- Exact cache/retained-run agreement; no provider is replayed by the cache. -/
theorem retainedNativeTargetRun_cache {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (u : SingleCode) :
    (retainedNativeTargetRun entry inverseLabel table L q u).cached.targetCache=
      (retainedNativeTargetRun entry inverseLabel table L q u).providerPrograms.map PacketWordEvaluation.value := rfl

/-- Projection of the actual retained target-provider primitive traces.
The sum's traversal/counter arithmetic and other structure are not charged. -/
def RetainedNativeTargetResult.providerActions {m L q : ℕ} (r : RetainedNativeTargetResult m L q) : ℕ :=
  (r.providerPrograms.toList.map (fun run => run.trace.booleanActions)).sum


theorem retainedNativeTargetRun_providerActions_bound {m n k : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) :
    (retainedNativeTargetRun entry inverseLabel table L q u).providerActions≤
      (cachePrecisionBudget L q+1)*nativeProviderQueryCoefficient k*(cachePrecisionBudget L q+5)^2 := by
  let P:=numericalDemand L (Nat.clog 2 (q+1))
  have hP : P≤cachePrecisionBudget L q := numericalDemand_precision_bound L q
  simp only [RetainedNativeTargetResult.providerActions,retainedNativeTargetRun,buildNativeTargetPrograms,
    List.Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change (∑ r : Fin (P+1),((prepareNativeSingleInput u).packetProgram r.val).trace.booleanActions)≤_
  calc
    _≤∑ _r : Fin (P+1),nativeProviderQueryCoefficient k*(cachePrecisionBudget L q+5)^2 := by
      apply Finset.sum_le_sum
      intro r _
      apply (nativeProviderPacketProgram_booleanActions hu r.val).trans
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _=(P+1)*(nativeProviderQueryCoefficient k*(cachePrecisionBudget L q+5)^2) := by simp
    _≤_ := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
        (nativeProviderQueryCoefficient k*(cachePrecisionBudget L q+5)^2) (Nat.add_le_add_right hP 1)


def nativeProviderCacheCoefficient (k L : ℕ) : ℕ :=
  (51200000*(L+1)+1)*nativeProviderQueryCoefficient k*(51200000*(L+1)+5)^2


theorem nativeProviderCache_algebra (A Q x : ℕ) (hx : 1≤x) :
    (A*x^9+1)*Q*(A*x^9+5)^2≤((A+1)*Q*(A+5)^2)*x^27 := by
  have hy : 1≤x^9 := Nat.one_le_pow _ _ hx
  have h1 : A*x^9+1≤(A+1)*x^9 := by nlinarith
  have h5 : A*x^9+5≤(A+5)*x^9 := by nlinarith
  apply (Nat.mul_le_mul (Nat.mul_le_mul_right Q h1) (Nat.pow_le_pow_left h5 2)).trans_eq
  ring


theorem retainedNativeTargetRun_providerActions_polynomial {m n k : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ)
    {wire : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) :
    (retainedNativeTargetRun entry inverseLabel table L q u).providerActions≤
      nativeProviderCacheCoefficient k L*(q+1)^27 := by
  apply (retainedNativeTargetRun_providerActions_bound entry inverseLabel table L q hu).trans
  exact nativeProviderCache_algebra (51200000*(L+1)) (nativeProviderQueryCoefficient k) (q+1) (by omega)


def nativeProviderCachePolynomialConstant (L : ℕ) : ℕ :=
  (51200000*(L+1)+1)*(20000*80000004^2*22080)*(51200000*(L+1)+5)^2


theorem nativeProviderCacheCoefficient_polynomial (k L : ℕ) :
    nativeProviderCacheCoefficient k L≤nativeProviderCachePolynomialConstant L*(k+3)^15 := by
  simpa only [nativeProviderCacheCoefficient,nativeProviderCachePolynomialConstant,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
    Nat.mul_le_mul_right ((51200000*(L+1)+5)^2)
      (Nat.mul_le_mul_left (51200000*(L+1)+1) (nativeProviderQueryCoefficient_polynomial k))

end EffectiveEncoding
