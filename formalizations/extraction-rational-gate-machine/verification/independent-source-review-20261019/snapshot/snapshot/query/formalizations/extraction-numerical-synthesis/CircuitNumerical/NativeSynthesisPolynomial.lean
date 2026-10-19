import CircuitNumerical.NativeTraceRefinement
import CircuitNumerical.RawOperationGrowth
import CircuitNumerical.NativeBudgetAlgebra

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096



abbrev nativeDataExpressionOracle (f : NativePacketDataOracle) : NativePacketExpressionOracle :=
  fun q => .literal (f q)

theorem nativeCachedPacketOracle_data {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) :
    nativeCachedPacketOracle cache=nativeDataExpressionOracle (fun r => readNativePacketCache cache r) := rfl

/-- Polynomial numerical Boolean action bound for the actual native value
program. All represented operand and operation bounds are derived here from
the binary input height, fixed table length and explicit recursion. Provider
execution, cache/list construction, indexing and control/counter arithmetic
are not identified with this numerical charge. -/
theorem nativeDataPairWord_booleanActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A a : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,IntegerPacketHeight (entry i r).decode (A*(p+1)^a))
    (hf : ∀ r,IntegerPacketHeight (f r).decode (A*(p+1)^a)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (nativeTracedPairWord (fun i => nativeDataExpressionOracle (entry i)) inverseLabel table
      (Nat.clog 2 (p+1)) (nativeDataExpressionOracle f)).booleanActions≤
      40000*(40*C+4)^2*(20*O)*(p+1)^(2*a+320) := by
  dsimp only
  let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
  let O:=1020*(n+1)*(2*L+1)*offsetGrowth
  have hbit0:=nativeDataPairWord_integerBitBudget entry inverseLabel table L (Nat.clog 2 (p+1))
    (A*(p+1)^a) hL f he hf
  have hprecision:=nativeBudget_precision_product (1000000000002*(n+1)) (L+1) A (p+1) a
    (traceRGrowth^Nat.clog 2 (p+1)) traceRGrowth (by omega) (traceRGrowth_precision_bound p)
  have hactualB : (nativeTracedPairWord (fun i => nativeDataExpressionOracle (entry i)) inverseLabel table
      (Nat.clog 2 (p+1)) (nativeDataExpressionOracle f)).integerBitBudget≤(20*C)*(p+1)^(a+128) :=
    hbit0.trans hprecision
  have hops0:=nativeDataPairWord_operations entry inverseLabel table L (Nat.clog 2 (p+1)) hL f
  have hoperationPrecision:=nativeBudget_operations_product (1020*(n+1)*(2*L+1)) (p+1)
    (offsetGrowth^Nat.clog 2 (p+1)) offsetGrowth (offsetGrowth_precision_bound p)
  have hactualO : (nativeTracedPairWord (fun i => nativeDataExpressionOracle (entry i)) inverseLabel table
      (Nat.clog 2 (p+1)) (nativeDataExpressionOracle f)).operations≤(20*O)*(p+1)^64 :=
    hops0.trans hoperationPrecision
  have h:=nativeTracedPairWord_booleanActions_power_bound (fun i => nativeDataExpressionOracle (entry i))
    inverseLabel table _ (nativeDataExpressionOracle f) p (a+128) 64 (20*C) (20*O) hactualB hactualO
  exact h.trans_eq (nativeBudget_charge_normalization C O (p+1) a)

theorem readNativeBuiltCache_height (f : NativePacketDataOracle) (P B : ℕ)
    (hf : ∀ r,r≤P → IntegerPacketHeight (f r).decode B) (r : ℕ) :
    IntegerPacketHeight (readNativePacketCache (buildNativePacketCache f P) r).decode B := by
  by_cases hr : r≤P
  · rw [readNativePacketCache_build f P r hr]
    exact hf r hr
  · rw [readNativePacketCache_default _ r (by omega),wordPacketOne_decode]
    exact IntegerPacketHeight.mono _ 0 B IntegerPacket.one_height (Nat.zero_le B)

/-- The actual eager-cache native synthesis. Only finite precision-indexed
input word heights are hypotheses. Neither a final budget/correctness
certificate nor a provider running-time assumption is hidden here. -/
theorem nativeCachedRun_booleanActions {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A a : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) →
      IntegerPacketHeight (entry i r).decode (A*(p+1)^a))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) →
      IntegerPacketHeight (f r).decode (A*(p+1)^a)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (nativeCachedRun entry inverseLabel table L p f).program.booleanActions≤
      40000*(40*C+4)^2*(20*O)*(p+1)^(2*a+320) := by
  let P:=numericalDemand L (Nat.clog 2 (p+1))
  let gates:=fun i r => readNativePacketCache (buildNativePacketCache (entry i) P) r
  let target:=fun r => readNativePacketCache (buildNativePacketCache f P) r
  have h:=nativeDataPairWord_booleanActions gates inverseLabel table L p A a hL target
    (fun i r => readNativeBuiltCache_height (entry i) P _ (he i) r)
    (fun r => readNativeBuiltCache_height f P _ hf r)
  dsimp only [nativeCachedRun]
  simp only [List.Vector.get_ofFn,nativeCachedPacketOracle_data]
  exact h

theorem nativeCachedRun_booleanActions_degree338 {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (entry i r).decode (A*(p+1)^9))
    (hf : ∀ r,r≤numericalDemand L (Nat.clog 2 (p+1)) → IntegerPacketHeight (f r).decode (A*(p+1)^9)) :
    let C:=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (nativeCachedRun entry inverseLabel table L p f).program.booleanActions≤
      40000*(40*C+4)^2*(20*O)*(p+1)^338 :=
  nativeCachedRun_booleanActions entry inverseLabel table L p A 9 hL f he hf

end CircuitRecursion
