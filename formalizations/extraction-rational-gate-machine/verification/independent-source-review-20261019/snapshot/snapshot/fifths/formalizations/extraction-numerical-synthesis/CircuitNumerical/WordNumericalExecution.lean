import CircuitNumerical.WordExpressionBudgets

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

inductive WordDecisionTrace where
  | minimum : WordMinimumTrace → WordDecisionTrace
  | comparison : WordScalarComparisonResult → WordDecisionTrace

structure WordArithmeticResult (m : ℕ) where
  result : ArithmeticWordResult m
  evaluations : List ScalarWordEvaluation
  decisions : List WordDecisionTrace

def wordTracedBase {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) : WordArithmeticResult m :=
  let scores:=List.Vector.ofFn (fun j => expressionDistance f (expressionWord entry (table j)) 20)
  let stored:=scores.map ScalarExpression.wordRun
  let minimum:=wordMinimumProgram n (stored.map ScalarWordEvaluation.value)
  ⟨⟨table minimum.index,scores.toList,n⟩,stored.toList,[.minimum minimum.trace]⟩

theorem wordTracedBase_result {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    (wordTracedBase entry table f).result=tracedBase entry table f := by
  rw [←integerTracedBase_eq]
  have hget (scores : List.Vector ScalarExpression (n+1)) :
      (scores.map ScalarExpression.integerProgramRun).get=(fun i => (scores.get i).integerProgramRun) := by
    funext i
    simp only [List.Vector.get_map]
  simp only [wordTracedBase,integerTracedBase,wordMinimumProgram_index,List.Vector.get_map,
    ScalarExpression.wordRun_decode,hget]

theorem wordTracedBase_evaluations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) :
    (wordTracedBase entry table f).evaluations=
      (wordTracedBase entry table f).result.expressions.map ScalarExpression.wordRun := by rfl

/-- Each score/threshold AST is evaluated once. Its actual Boolean fraction
comparison selects the branch, and both local runs and the decision are
retained. Only the chosen recursive correction branches are executed. -/
def wordTracedCorrection {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → WordArithmeticResult m)
    (t : ℕ) (f : PacketExpressionOracle) : WordArithmeticResult m :=
  let u:=approx f
  let residual:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.result.word))
  let score:=expressionDistance residual expressionPacketOne (2*t+2)
  let threshold:=ScalarExpression.stoppingThreshold t
  let scoreRun:=score.wordRun
  let thresholdRun:=threshold.wordRun
  let comparison:=wordScalarLEProgram scoreRun.value thresholdRun.value
  if comparison.le then
    ⟨⟨u.result.word,u.result.expressions++[score,threshold],u.result.comparisons+1⟩,
      u.evaluations++[scoreRun,thresholdRun],u.decisions++[.comparison comparison]⟩
  else
    let a:=approx (expressionFactorX residual t)
    let b:=approx (expressionFactorY residual t)
    ⟨⟨u.result.word++instructionInverse inverseLabel b.result.word++instructionInverse inverseLabel a.result.word++
        b.result.word++a.result.word,
      u.result.expressions++[score,threshold]++a.result.expressions++b.result.expressions,
      u.result.comparisons+a.result.comparisons+b.result.comparisons+1⟩,
      u.evaluations++[scoreRun,thresholdRun]++a.evaluations++b.evaluations,
      u.decisions++[.comparison comparison]++a.decisions++b.decisions⟩

theorem wordTracedCorrection_result {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → WordArithmeticResult m)
    (t : ℕ) (f : PacketExpressionOracle) :
    (wordTracedCorrection entry inverseLabel approx t f).result=
      tracedCorrection entry inverseLabel (fun g => (approx g).result) t f := by
  simp only [wordTracedCorrection,tracedCorrection,wordScalarLEProgram_value,ScalarExpression.wordRun_correct]
  split_ifs <;> rfl

theorem wordTracedCorrection_evaluations {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → WordArithmeticResult m)
    (ha : ∀ f,(approx f).evaluations=(approx f).result.expressions.map ScalarExpression.wordRun)
    (t : ℕ) (f : PacketExpressionOracle) :
    (wordTracedCorrection entry inverseLabel approx t f).evaluations=
      (wordTracedCorrection entry inverseLabel approx t f).result.expressions.map ScalarExpression.wordRun := by
  unfold wordTracedCorrection
  dsimp only
  split_ifs <;> simp only [ha,List.map_append,List.map_cons,List.map_nil]

def wordTracedPairWord {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → PacketExpressionOracle → WordArithmeticResult m
  | 0 => wordTracedBase entry table
  | k+1 => wordTracedCorrection entry inverseLabel
      (wordTracedCorrection entry inverseLabel (wordTracedPairWord entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem wordTracedPairWord_result {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    (wordTracedPairWord entry inverseLabel table k f).result=tracedPairWord entry inverseLabel table k f := by
  induction k generalizing f with
  | zero => exact wordTracedBase_result entry table f
  | succ k ih => simp only [wordTracedPairWord,tracedPairWord,wordTracedCorrection_result,ih]

theorem wordTracedPairWord_evaluations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle) :
    (wordTracedPairWord entry inverseLabel table k f).evaluations=
      (wordTracedPairWord entry inverseLabel table k f).result.expressions.map ScalarExpression.wordRun := by
  induction k generalizing f with
  | zero => exact wordTracedBase_evaluations entry table f
  | succ k ih =>
    exact wordTracedCorrection_evaluations entry inverseLabel _
      (fun g => wordTracedCorrection_evaluations entry inverseLabel _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

def WordDecisionTrace.actions : WordDecisionTrace → ℕ
  | .minimum trace => trace.actions
  | .comparison run => run.actions+4

def WordArithmeticResult.evaluationActions {m : ℕ} (r : WordArithmeticResult m) : ℕ :=
  (r.evaluations.map (fun run => run.trace.booleanActions)).sum

def WordArithmeticResult.decisionActions {m : ℕ} (r : WordArithmeticResult m) : ℕ :=
  (r.decisions.map WordDecisionTrace.actions).sum

def WordArithmeticResult.booleanActions {m : ℕ} (r : WordArithmeticResult m) : ℕ :=
  r.evaluationActions+r.decisionActions

end CircuitRecursion
