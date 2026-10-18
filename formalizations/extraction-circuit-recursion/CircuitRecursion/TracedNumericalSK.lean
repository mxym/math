import CircuitRecursion.FactorExpressions

namespace CircuitRecursion

def expressionWord {m : ℕ} (entry : Fin m → PacketExpressionOracle) :
    List (Fin m) → PacketExpressionOracle
  | [] => expressionPacketOne
  | i::w => expressionPacketMul (expressionWord entry w) (entry i)

@[simp] theorem expressionWord_eval {m : ℕ} (entry : Fin m → PacketExpressionOracle) (w : List (Fin m)) :
    evaluatePacketOracle (expressionWord entry w)=quaternionWordOracle (fun i => evaluatePacketOracle (entry i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [expressionWord,expressionPacketMul_eval,ih,quaternionWordOracle]

structure ArithmeticWordResult (m : ℕ) where
  word : List (Fin m)
  expressions : List ScalarExpression
  comparisons : ℕ

def ArithmeticWordResult.operations {m : ℕ} (r : ArithmeticWordResult m) : ℕ :=
  (r.expressions.map ScalarExpression.operations).sum+r.comparisons

def tracedBase {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) : ArithmeticWordResult m :=
  let scores := List.Vector.ofFn (fun j => expressionDistance f (expressionWord entry (table j)) 20)
  let values := scores.map ScalarExpression.eval
  ⟨table (rationalMinIndex n values.get),scores.toList,n⟩

theorem tracedBase_word {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    (tracedBase entry table f).word=
      fixedNetWord (fun i => evaluatePacketOracle (entry i)) table (evaluatePacketOracle f) := by
  have hs : (fun j => ((List.Vector.ofFn
      (fun j => expressionDistance f (expressionWord entry (table j)) 20)).map ScalarExpression.eval).get j)=
      (List.Vector.ofFn (fun j => distanceScore (evaluatePacketOracle f)
        (quaternionWordOracle (fun i => evaluatePacketOracle (entry i)) (table j)) 20)).get := by
    funext j
    simp only [List.Vector.get_map,List.Vector.get_ofFn,expressionDistance_eval,expressionWord_eval]
  simpa only [tracedBase,fixedNetWord,hs]

def tracedCorrection {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (t : ℕ) (f : PacketExpressionOracle) : ArithmeticWordResult m :=
  let u := approx f
  let residual := expressionPacketMul f (expressionPacketInverse (expressionWord entry u.word))
  let score := expressionDistance residual expressionPacketOne (2*t+2)
  if score.eval≤(ScalarExpression.stoppingThreshold t).eval then
    ⟨u.word,u.expressions++[score,.stoppingThreshold t],u.comparisons+1⟩
  else
    let a := approx (expressionFactorX residual t)
    let b := approx (expressionFactorY residual t)
    ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
      u.expressions++[score,.stoppingThreshold t]++a.expressions++b.expressions,
      u.comparisons+a.comparisons+b.comparisons+1⟩

theorem tracedCorrection_word {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (plain : QuaternionOracle → List (Fin m))
    (ha : ∀ f,(approx f).word=plain (evaluatePacketOracle f)) (t : ℕ) (f : PacketExpressionOracle) :
    (tracedCorrection entry inverseLabel approx t f).word=
      numericalCorrection (fun i => evaluatePacketOracle (entry i)) inverseLabel plain t (evaluatePacketOracle f) := by
  simp only [tracedCorrection,numericalCorrection,ha,expressionDistance_eval,
    expressionWord_eval,expressionPacketInverse_eval,expressionPacketMul_eval,
    expressionPacketOne_eval,expressionFactorX_eval,expressionFactorY_eval,
    residualSmall,decide_eq_true_eq,ScalarExpression.eval]
  split_ifs <;> rfl

def tracedPairWord {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → PacketExpressionOracle → ArithmeticWordResult m
  | 0 => tracedBase entry table
  | k+1 => tracedCorrection entry inverseLabel
      (tracedCorrection entry inverseLabel (tracedPairWord entry inverseLabel table k) (numericalThreshold k))
      (numericalThreshold k)

theorem tracedPairWord_word {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    (tracedPairWord entry inverseLabel table k f).word=
      numericalPairWord (fun i => evaluatePacketOracle (entry i)) inverseLabel table k (evaluatePacketOracle f) := by
  induction k generalizing f with
  | zero => exact tracedBase_word entry table f
  | succ k ih =>
    exact tracedCorrection_word entry inverseLabel _ _
      (fun g => tracedCorrection_word entry inverseLabel _ _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

end CircuitRecursion
