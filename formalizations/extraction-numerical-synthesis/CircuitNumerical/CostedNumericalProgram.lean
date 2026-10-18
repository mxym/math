import CircuitNumerical.CostedIntegerEvaluation

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure CostedArithmeticWordResult (m : ℕ) where
  result : ArithmeticWordResult m
  rootCharge : ℕ

def costedTracedBase {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) : CostedArithmeticWordResult m :=
  let scores:=List.Vector.ofFn (fun j => expressionDistance f (expressionWord entry (table j)) 20)
  let stored:=scores.map ScalarExpression.costedIntegerRun
  let j:=integerMinIndex n (fun i => (stored.get i).value)
  ⟨⟨table j,scores.toList,n⟩,∑ i : Fin (n+1),(stored.get i).rootCharge⟩

theorem costedTracedBase_result {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    (costedTracedBase entry table f).result=tracedBase entry table f := by
  rw [← integerTracedBase_eq]
  have hget (scores : List.Vector ScalarExpression (n+1)) :
      (scores.map ScalarExpression.integerProgramRun).get=(fun i => (scores.get i).integerProgramRun) := by
    funext i
    simp only [List.Vector.get_map]
  simp only [costedTracedBase,integerTracedBase,List.Vector.get_map,
    ScalarExpression.costedIntegerRun_value,hget]

theorem costedTracedBase_rootCharge {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    (costedTracedBase entry table f).rootCharge≤
      (costedTracedBase entry table f).result.binaryRootPrimitiveOperations := by
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) =>
    ScalarExpression.costedIntegerRun_rootCharge (expressionDistance f (expressionWord entry (table i)) 20))
  simpa only [costedTracedBase,ArithmeticWordResult.binaryRootPrimitiveOperations,List.Vector.get_map,
    List.Vector.get_ofFn,List.Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hs

def costedTracedCorrection {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → CostedArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) : CostedArithmeticWordResult m :=
  let u:=approx f
  let residual:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.result.word))
  let score:=expressionDistance residual expressionPacketOne (2*t+2)
  let threshold:=ScalarExpression.stoppingThreshold t
  let scoreRun:=score.costedIntegerRun
  let thresholdRun:=threshold.costedIntegerRun
  if scoreRun.value.crossLE thresholdRun.value then
    ⟨⟨u.result.word,u.result.expressions++[score,threshold],u.result.comparisons+1⟩,
      u.rootCharge+scoreRun.rootCharge+thresholdRun.rootCharge⟩
  else
    let a:=approx (expressionFactorX residual t)
    let b:=approx (expressionFactorY residual t)
    ⟨⟨u.result.word++instructionInverse inverseLabel b.result.word++instructionInverse inverseLabel a.result.word++
        b.result.word++a.result.word,
      u.result.expressions++[score,threshold]++a.result.expressions++b.result.expressions,
      u.result.comparisons+a.result.comparisons+b.result.comparisons+1⟩,
      u.rootCharge+scoreRun.rootCharge+thresholdRun.rootCharge+a.rootCharge+b.rootCharge⟩

theorem costedTracedCorrection_result {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → CostedArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) :
    (costedTracedCorrection entry inverseLabel approx t f).result=
      tracedCorrection entry inverseLabel (fun g => (approx g).result) t f := by
  simp only [costedTracedCorrection,tracedCorrection,IntegerScalar.crossLE_value,
    ScalarExpression.costedIntegerRun_correct]
  split_ifs <;> rfl

theorem costedTracedCorrection_rootCharge {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → CostedArithmeticWordResult m)
    (ha : ∀ f,(approx f).rootCharge≤(approx f).result.binaryRootPrimitiveOperations)
    (t : ℕ) (f : PacketExpressionOracle) :
    (costedTracedCorrection entry inverseLabel approx t f).rootCharge≤
      (costedTracedCorrection entry inverseLabel approx t f).result.binaryRootPrimitiveOperations := by
  let u:=approx f
  let residual:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.result.word))
  let score:=expressionDistance residual expressionPacketOne (2*t+2)
  let threshold:=ScalarExpression.stoppingThreshold t
  let a:=approx (expressionFactorX residual t)
  let b:=approx (expressionFactorY residual t)
  have hu : u.rootCharge≤u.result.binaryRootPrimitiveOperations := ha f
  have haa : a.rootCharge≤a.result.binaryRootPrimitiveOperations := ha _
  have hbb : b.rootCharge≤b.result.binaryRootPrimitiveOperations := ha _
  have hs:=ScalarExpression.costedIntegerRun_rootCharge score
  have ht:=ScalarExpression.costedIntegerRun_rootCharge threshold
  simp only [ArithmeticWordResult.binaryRootPrimitiveOperations] at hu haa hbb
  unfold costedTracedCorrection
  dsimp only
  split_ifs
  · change u.rootCharge+score.costedIntegerRun.rootCharge+threshold.costedIntegerRun.rootCharge≤
      ((u.result.expressions++[score,threshold]).map ScalarExpression.binaryRootPrimitiveOperations).sum
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
    omega
  · change u.rootCharge+score.costedIntegerRun.rootCharge+threshold.costedIntegerRun.rootCharge+a.rootCharge+b.rootCharge≤
      ((u.result.expressions++[score,threshold]++a.result.expressions++b.result.expressions).map
        ScalarExpression.binaryRootPrimitiveOperations).sum
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
    omega

def costedTracedPairWord {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → PacketExpressionOracle → CostedArithmeticWordResult m
  | 0 => costedTracedBase entry table
  | k+1 => costedTracedCorrection entry inverseLabel
      (costedTracedCorrection entry inverseLabel (costedTracedPairWord entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem costedTracedPairWord_result {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    (costedTracedPairWord entry inverseLabel table k f).result=tracedPairWord entry inverseLabel table k f := by
  induction k generalizing f with
  | zero => exact costedTracedBase_result entry table f
  | succ k ih =>
    simp only [costedTracedPairWord,tracedPairWord,costedTracedCorrection_result,ih]

theorem costedTracedPairWord_rootCharge {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    (costedTracedPairWord entry inverseLabel table k f).rootCharge≤
      (costedTracedPairWord entry inverseLabel table k f).result.binaryRootPrimitiveOperations := by
  induction k generalizing f with
  | zero => exact costedTracedBase_rootCharge entry table f
  | succ k ih =>
    exact costedTracedCorrection_rootCharge entry inverseLabel _
      (fun g => costedTracedCorrection_rootCharge entry inverseLabel _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

def costedCachedArithmeticRun {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : QuaternionOracle) : CostedArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (p+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildPacketCache (entry i) P)
  let targetCache:=buildPacketCache target P
  costedTracedPairWord (fun i q => .literal (readPacketCache (gates.get i).1 q)) inverseLabel table
    (Nat.clog 2 (p+1)) (fun q => .literal (readPacketCache targetCache.1 q))

theorem costedCachedArithmeticRun_result {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    (costedCachedArithmeticRun entry inverseLabel table L p f).result=cachedArithmeticRun entry inverseLabel table L p f := by
  exact costedTracedPairWord_result _ inverseLabel table _ _

theorem costedCachedArithmeticRun_rootCharge {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) :
    (costedCachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).rootCharge≤
      (16*cachedIntegerBudgetConstant n L+37)*(1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^201 := by
  have h : (costedCachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).rootCharge≤
      (costedCachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
        (dyadicQuaternionOracle f)).result.binaryRootPrimitiveOperations := costedTracedPairWord_rootCharge _ _ _ _ _
  rw [costedCachedArithmeticRun_result] at h
  exact h.trans (cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial entry G he inverseLabel table L p hL f U hf)

end CircuitRecursion
