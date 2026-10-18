import CircuitNumerical.InputNumericalPower
import CircuitNumerical.NativeBudgetAlgebra

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem inputScalarList_refines_budget {m P : ℕ} (cache : NativeCacheEnvironment m P)
    {es : List (InputScalarExpression m)} {Es : List ScalarExpression}
    (h : List.Forall₂ (fun e E => NativeScalarRefines (e.resolve cache) E) es Es) :
    (es.map (fun e => e.integerBitBudget cache)).sum≤20*(Es.map ScalarExpression.integerBitBudget).sum := by
  induction h with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons he ht ih =>
    have hb:=he.budget_le
    dsimp only [InputScalarExpression.integerBitBudget] at ih ⊢
    simp only [List.map_cons,List.sum_cons]
    omega

theorem InputArithmeticRefines.budget_le {m P : ℕ} {cache : NativeCacheEnvironment m P}
    {r : InputArithmeticWordResult m} {R : ArithmeticWordResult m} (h : InputArithmeticRefines cache r R) :
    r.integerBitBudget cache≤20*R.integerBitBudget :=
  inputScalarList_refines_budget cache h.expressions

theorem inputTracedCache_integerBitBudget {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k A : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,IntegerPacketHeight (nativeCacheInputRead cache (.gate i) r).packet.decode A)
    (hf : ∀ r,IntegerPacketHeight (nativeCacheInputRead cache .target r).packet.decode A) :
    (inputTracedPairWord cache inputGateOracle inverseLabel table k (inputTargetOracle m)).integerBitBudget cache≤
      20*(1000000000002*(n+1)*(8*(A+1)+2)*(L+1)*traceRGrowth^k) := by
  let E:=fun i => rawPacketExpressionOracle (fun q => (nativeCacheInputRead cache (.gate i) q).packet.decode)
  let F:=rawPacketExpressionOracle (fun q => (nativeCacheInputRead cache .target q).packet.decode)
  have href:=inputTracedPairWord_refines cache (entry:=inputGateOracle) (E:=E)
    (fun i => inputCacheLeaf_refines cache (.gate i)) inverseLabel table k
    (f:=inputTargetOracle m) (F:=F) (inputCacheLeaf_refines cache .target)
  have hbit:=tracedPairWord_flat_integerBitBudget E (8*(A+1))
    (fun i => rawPacketExpressionOracle_bitEnvelope _ A (he i)) inverseLabel table L k hL F
    (rawPacketExpressionOracle_bitEnvelope _ A hf)
  exact href.budget_le.trans (Nat.mul_le_mul_left 20 hbit)

/-- The input-reference value program is bounded directly, from its actual
retained evaluations and decisions. Resolution is used only to prove the
operand and expression budgets, never to execute the program. -/
theorem inputTracedCache_numericalActions {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A a : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,IntegerPacketHeight (nativeCacheInputRead cache (.gate i) r).packet.decode (A*(p+1)^a))
    (hf : ∀ r,IntegerPacketHeight (nativeCacheInputRead cache .target r).packet.decode (A*(p+1)^a)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (inputTracedPairWord cache inputGateOracle inverseLabel table (Nat.clog 2 (p+1))
      (inputTargetOracle m)).numericalActions≤40000*(40*C+4)^2*(20*O)*(p+1)^(2*a+320) := by
  dsimp only
  let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
  let O:=1020*(n+1)*(2*L+1)*offsetGrowth
  have hbit0:=inputTracedCache_integerBitBudget cache inverseLabel table L (Nat.clog 2 (p+1))
    (A*(p+1)^a) hL he hf
  have hprecision:=nativeBudget_precision_product (1000000000002*(n+1)) (L+1) A (p+1) a
    (traceRGrowth^Nat.clog 2 (p+1)) traceRGrowth (by omega) (traceRGrowth_precision_bound p)
  have hactualB : (inputTracedPairWord cache inputGateOracle inverseLabel table
      (Nat.clog 2 (p+1)) (inputTargetOracle m)).integerBitBudget cache≤(20*C)*(p+1)^(a+128) :=
    hbit0.trans hprecision
  have hops0:=inputTracedCache_operations cache inverseLabel table L p hL
  have hactualO : (inputTracedPairWord cache inputGateOracle inverseLabel table
      (Nat.clog 2 (p+1)) (inputTargetOracle m)).operations cache≤(20*O)*(p+1)^64 := by
    simpa only [O,Nat.mul_assoc] using hops0
  have h:=inputTracedPairWord_numericalActions_power_bound cache inputGateOracle inverseLabel table _
    (inputTargetOracle m) p (a+128) 64 (20*C) (20*O) hactualB hactualO
  exact h.trans_eq (nativeBudget_charge_normalization C O (p+1) a)

theorem inputCachedRun_gate_height {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p B : ℕ)
    (f : NativePacketDataOracle) (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) →
      IntegerPacketHeight (entry i r).decode B) (i : Fin m) (r : ℕ) :
    IntegerPacketHeight (nativeCacheInputRead (inputCachedRun entry inverseLabel table L p f).cache (.gate i) r).packet.decode B := by
  change IntegerPacketHeight (nativeLinearReadGatePacket
    (List.Vector.ofFn (fun i : Fin m => buildNativePacketCache (entry i) (numericalDemand L (Nat.clog 2 (p+1)))))
    (buildNativePacketCache f (numericalDemand L (Nat.clog 2 (p+1)))) i r).packet.decode B
  rw [nativeLinearReadGatePacket_packet,List.Vector.get_ofFn]
  exact readNativeBuiltCache_height (entry i) _ B (he i) r

theorem inputCachedRun_target_height {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p B : ℕ)
    (f : NativePacketDataOracle) (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) →
      IntegerPacketHeight (f r).decode B) (r : ℕ) :
    IntegerPacketHeight (nativeCacheInputRead (inputCachedRun entry inverseLabel table L p f).cache .target r).packet.decode B := by
  change IntegerPacketHeight (nativeLinearReadPacketCache
    (buildNativePacketCache f (numericalDemand L (Nat.clog 2 (p+1)))) r).packet.decode B
  rw [nativeLinearReadPacketCache_packet]
  exact readNativeBuiltCache_height f _ B hf r

/-- Numerical charge of the same eager-cache program whose concrete cache
reads are retained. The only input-size hypotheses are finite provider
output heights; provider execution is not charged here. -/
theorem inputCachedRun_numericalActions_degree338 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p A : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (entry i r).decode (A*(p+1)^9))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (f r).decode (A*(p+1)^9)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (inputCachedRun entry inverseLabel table L p f).program.numericalActions≤
      40000*(40*C+4)^2*(20*O)*(p+1)^338 :=
  inputTracedCache_numericalActions (inputCachedRun entry inverseLabel table L p f).cache inverseLabel table
    L p A 9 hL (inputCachedRun_gate_height entry inverseLabel table L p _ f he)
    (inputCachedRun_target_height entry inverseLabel table L p _ f hf)

/-- Numerical Boolean primitives and executed cache list-spines, both read
from this one actual retained program. This is a partial source-cost model:
provider runs, cache/AST/list construction, general control/index arithmetic,
allocation and evaluating the cost projections remain separate. -/
def InputArithmeticWordResult.onlineActions {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  r.numericalActions+r.readActions

theorem inputCachedRun_onlineActions_degree338 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p A : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (entry i r).decode (A*(p+1)^9))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (f r).decode (A*(p+1)^9)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (inputCachedRun entry inverseLabel table L p f).program.onlineActions≤
      (40000*(40*C+4)^2*(20*O)+80*(m+51200000*(L+1)+5)*O)*(p+1)^338 := by
  have hn:=inputCachedRun_numericalActions_degree338 entry inverseLabel table L p A hL f he hf
  have hr:=inputCachedRun_readActions_degree73 entry inverseLabel table L p hL f
  have hp : (p+1)^73≤(p+1)^338 := Nat.pow_le_pow_right (by omega) (by decide)
  have hrr:=hr.trans (Nat.mul_le_mul_left _ hp)
  exact (Nat.add_le_add hn hrr).trans_eq (Nat.add_mul _ _ _).symm

end CircuitRecursion
