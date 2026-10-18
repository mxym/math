import CircuitNumerical.InputCachedSynthesis
import CircuitNumerical.RawOperationGrowth

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem inputCacheLeaf_refines {m P : ℕ} (cache : NativeCacheEnvironment m P) (label : NativeCacheLabel m) :
    NativePacketOracleRefines (resolveInputPacketOracle cache (fun q => .input label q))
      (rawPacketExpressionOracle (fun q => (nativeCacheInputRead cache label q).packet.decode)) :=
  fun q => NativePacketRefines.raw (nativeCacheInputRead cache label q).packet

theorem inputTracedCache_operations {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (inputTracedPairWord cache inputGateOracle inverseLabel table (Nat.clog 2 (p+1)) (inputTargetOracle m)).operations cache≤
      20*((1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64) := by
  let E:=fun i => rawPacketExpressionOracle (fun q => (nativeCacheInputRead cache (.gate i) q).packet.decode)
  let F:=rawPacketExpressionOracle (fun q => (nativeCacheInputRead cache .target q).packet.decode)
  have href:=inputTracedPairWord_refines cache (entry:=inputGateOracle) (E:=E)
    (fun i => inputCacheLeaf_refines cache (.gate i)) inverseLabel table (Nat.clog 2 (p+1))
    (f:=inputTargetOracle m) (F:=F) (inputCacheLeaf_refines cache .target)
  have hops:=tracedPairWord_twenty_precision_operations E (fun i => rawPacketExpressionOracle_operationBound _)
    inverseLabel table L p hL F (rawPacketExpressionOracle_operationBound _)
  exact href.operations_le.trans (Nat.mul_le_mul_left 20 hops)

def InputArithmeticWordResult.readCount {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  (r.evaluations.map (fun e => e.reads.length)).sum

theorem InputArithmeticWordResult.readCount_bound {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P)
    (hmatch : r.evaluations=r.expressions.map (fun e => e.inputRun cache)) : r.readCount≤r.operations cache := by
  have hs : (r.expressions.map (fun e => (e.inputRun cache).reads.length)).sum≤
      (r.expressions.map (fun e => (e.resolve cache).interpret.operations)).sum := by
    induction r.expressions with
    | nil => simp only [List.map_nil,List.sum_nil,le_refl]
    | cons e es ih =>
      have he:=InputScalarExpression.inputRun_reads_operations cache e
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add he ih
  simp only [InputArithmeticWordResult.readCount,hmatch,List.map_map]
  exact hs.trans (Nat.le_add_right _ _)

theorem inputTracedCache_readCount {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (inputTracedPairWord cache inputGateOracle inverseLabel table (Nat.clog 2 (p+1)) (inputTargetOracle m)).readCount≤
      20*((1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64) := by
  exact (InputArithmeticWordResult.readCount_bound _ cache
    (inputTracedPairWord_evaluations cache inputGateOracle inverseLabel table _ _)).trans
      (inputTracedCache_operations cache inverseLabel table L p hL)

theorem inputTracedCache_readActions {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) :
    (inputTracedPairWord cache inputGateOracle inverseLabel table (Nat.clog 2 (p+1)) (inputTargetOracle m)).readActions≤
      4*(m+P+5)*(20*((1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64)) := by
  exact (inputTracedPairWord_readActions cache inputGateOracle inverseLabel table _ _).trans
    (Nat.mul_le_mul_left _ (inputTracedCache_operations cache inverseLabel table L p hL))

/-- Record-free algebra for accumulating the actual online list-cache reads. -/
theorem inputCache_precision_fee_algebra (m P O Q C : ℕ) (hQ : 1≤Q) (hP : P≤C*Q^9) :
    4*(m+P+5)*(20*(O*Q^64))≤80*(m+C+5)*O*Q^73 := by
  have hpow : 1≤Q^9 := Nat.one_le_pow _ _ hQ
  have hbase : m+P+5≤(m+C+5)*Q^9 := by nlinarith
  have hm:=Nat.mul_le_mul_right (20*(O*Q^64)) (Nat.mul_le_mul_left 4 hbase)
  apply hm.trans_eq
  rw [show 73=9+64 by decide,pow_add]
  ring

theorem inputCachedRun_readCount {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (inputCachedRun entry inverseLabel table L p f).program.readCount≤
      20*((1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64) := by
  exact inputTracedCache_readCount (inputCachedRun entry inverseLabel table L p f).cache inverseLabel table L p hL

/-- The sum is over the concrete reads retained by this actual execution.
No provider runs during these online cache accesses. Provider generation,
cache/AST/list construction, control/counter arithmetic and full-machine
time are separate; this theorem charges the executed cache list-spines. -/
theorem inputCachedRun_readActions_degree73 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (inputCachedRun entry inverseLabel table L p f).program.readActions≤
      80*(m+51200000*(L+1)+5)*O*(p+1)^73 := by
  have h:=inputTracedCache_readActions (inputCachedRun entry inverseLabel table L p f).cache inverseLabel table L p hL
  have hpoly:=inputCache_precision_fee_algebra m (numericalDemand L (Nat.clog 2 (p+1)))
    (1020*(n+1)*(2*L+1)*offsetGrowth) (p+1) (51200000*(L+1)) (by omega)
    (numericalDemand_precision_bound L p)
  exact h.trans hpoly

end CircuitRecursion
