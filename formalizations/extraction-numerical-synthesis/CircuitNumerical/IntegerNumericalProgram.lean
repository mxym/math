import CircuitNumerical.IntegerExpressionProgram

namespace CircuitRecursion

def integerTracedBase {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) : ArithmeticWordResult m :=
  let scores:=List.Vector.ofFn (fun j => expressionDistance f (expressionWord entry (table j)) 20)
  let values:=scores.map ScalarExpression.integerProgramRun
  ⟨table (integerMinIndex n values.get),scores.toList,n⟩

theorem integerTracedBase_eq {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    integerTracedBase entry table f=tracedBase entry table f := by
  have hget (scores : List.Vector ScalarExpression (n+1)) :
      (scores.map ScalarExpression.eval).get=(fun i => (scores.get i).eval) := by
    funext i
    simp only [List.Vector.get_map]
  simp only [integerTracedBase,tracedBase,integerMinIndex_eq,List.Vector.get_map,
    ScalarExpression.integerProgramRun_correct,hget]

def integerTracedCorrection {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) : ArithmeticWordResult m :=
  let u:=approx f
  let residual:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.word))
  let score:=expressionDistance residual expressionPacketOne (2*t+2)
  if score.integerProgramRun.crossLE (ScalarExpression.stoppingThreshold t).integerProgramRun then
    ⟨u.word,u.expressions++[score,.stoppingThreshold t],u.comparisons+1⟩
  else
    let a:=approx (expressionFactorX residual t)
    let b:=approx (expressionFactorY residual t)
    ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
      u.expressions++[score,.stoppingThreshold t]++a.expressions++b.expressions,
      u.comparisons+a.comparisons+b.comparisons+1⟩

theorem integerTracedCorrection_eq {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) :
    integerTracedCorrection entry inverseLabel approx t f=tracedCorrection entry inverseLabel approx t f := by
  simp only [integerTracedCorrection,tracedCorrection,IntegerScalar.crossLE_value,
    ScalarExpression.integerProgramRun_correct]

theorem integerTracedCorrection_function {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) :
    integerTracedCorrection entry inverseLabel=tracedCorrection entry inverseLabel := by
  funext approx t f
  exact integerTracedCorrection_eq entry inverseLabel approx t f

def integerTracedPairWord {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → PacketExpressionOracle → ArithmeticWordResult m
  | 0 => integerTracedBase entry table
  | k+1 => integerTracedCorrection entry inverseLabel
      (integerTracedCorrection entry inverseLabel (integerTracedPairWord entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem integerTracedPairWord_eq {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : PacketExpressionOracle) :
    integerTracedPairWord entry inverseLabel table k f=tracedPairWord entry inverseLabel table k f := by
  induction k generalizing f with
  | zero => exact integerTracedBase_eq entry table f
  | succ k ih =>
    have hi : integerTracedPairWord entry inverseLabel table k=tracedPairWord entry inverseLabel table k :=
      funext ih
    simp only [integerTracedPairWord,tracedPairWord,integerTracedCorrection_function,hi]

/-- The actual eager-cache word program, with all online expression arithmetic
evaluated by raw integer operations and explicit binary division/sqrt. Every
base, stopping and Pauli-chart choice uses signed integer cross-products. -/
def integerCachedArithmeticRun {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : QuaternionOracle) : ArithmeticWordResult m :=
  let P:=numericalDemand L (Nat.clog 2 (p+1))
  let gates:=List.Vector.ofFn (fun i : Fin m => buildPacketCache (entry i) P)
  let targetCache:=buildPacketCache target P
  integerTracedPairWord (fun i q => .literal (readPacketCache (gates.get i).1 q)) inverseLabel table
    (Nat.clog 2 (p+1)) (fun q => .literal (readPacketCache targetCache.1 q))

theorem integerCachedArithmeticRun_eq {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    integerCachedArithmeticRun entry inverseLabel table L p f=cachedArithmeticRun entry inverseLabel table L p f := by
  simp only [integerCachedArithmeticRun,cachedArithmeticRun,integerTracedPairWord_eq]

theorem integerCachedArithmeticRun_rational_integerBitBudget {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketBitEnvelope
      (cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1)))) (0,B))
    (hf : PacketBitEnvelope
      (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) (0,B)) :
    (integerCachedArithmeticRun entry inverseLabel table L p f).integerBitBudget≤
      1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128 := by
  rw [integerCachedArithmeticRun_eq]
  exact cachedArithmeticRun_envelope_integerBitBudget entry inverseLabel table L p B hL f he hf

theorem integerCachedArithmeticSU2Synthesis {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → DyadicQuaternionOracle), (∀ i,DyadicQApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ (p : ℕ) (U : SU2) (f : DyadicQuaternionOracle),DyadicQApproximates f U →
        let r:=integerCachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
          (dyadicQuaternionOracle f)
        r.word.length≤32*L*(p+1)^5 ∧
        unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G r.word))≤(1/2:ℝ)^p ∧
        r.integerBitBudget≤cachedIntegerBudgetConstant n L*(p+1)^137 ∧
        r.binaryRootPrimitiveOperations≤
          (16*cachedIntegerBudgetConstant n L+37)*(1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^201 := by
  obtain ⟨L,n,table,hL,hcover⟩:=precomputedNet_exists G hinv huniversal
  refine ⟨L,n,table,fun entry he inverseLabel hi p U f hf => ?_⟩
  dsimp only
  rw [integerCachedArithmeticRun_eq]
  have hw : (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).word=
      numericalPairWord (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table
        (Nat.clog 2 (p+1)) (dyadicQuaternionOracle f) :=
    (cachedArithmeticRun_word _ inverseLabel table L p _).trans
      (cachedNumericalRun_word _ inverseLabel table L p hL _)
  refine ⟨?_,?_,cachedArithmeticRun_integerBitBudget entry G he inverseLabel table L p hL f U hf,
    cachedArithmeticRun_binaryRootPrimitiveOperations_polynomial entry G he inverseLabel table L p hL f U hf⟩
  · rw [hw]
    have ht:=numericalPairWord_length (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L hL
      (Nat.clog 2 (p+1)) (dyadicQuaternionOracle f)
    have hp:=Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · rw [hw]
    have ht:=numericalPairWord_error (fun i => dyadicQuaternionOracle (entry i)) G he inverseLabel hi table hcover
      (Nat.clog 2 (p+1)) U (dyadicQuaternionOracle f) hf
    have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision _ p hp)

end CircuitRecursion
