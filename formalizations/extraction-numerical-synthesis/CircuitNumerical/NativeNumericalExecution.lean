import CircuitNumerical.NativeFactorExpressions

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def nativeExpressionWord {m : ℕ} (entry : Fin m → NativePacketExpressionOracle) :
    List (Fin m) → NativePacketExpressionOracle
  | [] => nativeExpressionPacketOne
  | i::w => nativeExpressionPacketMul (nativeExpressionWord entry w) (entry i)

@[simp] theorem nativeExpressionWord_eval {m : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (w : List (Fin m)) : evaluateNativePacketOracle (nativeExpressionWord entry w)=
      quaternionWordOracle (fun i => evaluateNativePacketOracle (entry i)) w := by
  induction w with
  | nil => exact nativeExpressionPacketOne_eval
  | cons i w ih => simp only [nativeExpressionWord,nativeExpressionPacketMul_eval,ih,quaternionWordOracle]

structure NativeArithmeticWordResult (m : ℕ) where
  word : List (Fin m)
  expressions : List NativeScalarExpression
  comparisons : ℕ
  evaluations : List ScalarWordEvaluation
  decisions : List WordDecisionTrace

/-- Binary literal inputs flow through the native AST constructors and the
Boolean numerical programs. No semantic interpretation is executed here. -/
def nativeTracedBase {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : NativePacketExpressionOracle) : NativeArithmeticWordResult m :=
  let scores:=List.Vector.ofFn (fun j => nativeExpressionDistance f (nativeExpressionWord entry (table j)) 20)
  let stored:=scores.map NativeScalarExpression.wordRun
  let minimum:=wordMinimumProgram n (stored.map ScalarWordEvaluation.value)
  ⟨table minimum.index,scores.toList,n,stored.toList,[.minimum minimum.trace]⟩

theorem nativeTracedBase_word {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : NativePacketExpressionOracle) :
    (nativeTracedBase entry table f).word=
      fixedNetWord (fun i => evaluateNativePacketOracle (entry i)) table (evaluateNativePacketOracle f) := by
  simp only [nativeTracedBase,wordMinimumProgram_index,integerMinIndex_eq,List.Vector.get_map,
    List.Vector.get_ofFn,NativeScalarExpression.wordRun_correct,nativeExpressionDistance_eval,
    nativeExpressionWord_eval,fixedNetWord]
  congr 1
  congr 1
  funext i
  rw [List.Vector.get_ofFn]

theorem nativeTracedBase_evaluations {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : NativePacketExpressionOracle) :
    (nativeTracedBase entry table f).evaluations=
      (nativeTracedBase entry table f).expressions.map NativeScalarExpression.wordRun := by rfl

def nativeTracedCorrection {m : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : NativePacketExpressionOracle → NativeArithmeticWordResult m)
    (t : ℕ) (f : NativePacketExpressionOracle) : NativeArithmeticWordResult m :=
  let u:=approx f
  let residual:=nativeExpressionPacketMul f (nativeExpressionPacketInverse (nativeExpressionWord entry u.word))
  let score:=nativeExpressionDistance residual nativeExpressionPacketOne (2*t+2)
  let threshold:=NativeScalarExpression.stoppingThreshold t
  let scoreRun:=score.wordRun
  let thresholdRun:=threshold.wordRun
  let comparison:=wordScalarLEProgram scoreRun.value thresholdRun.value
  if comparison.le then
    ⟨u.word,u.expressions++[score,threshold],u.comparisons+1,
      u.evaluations++[scoreRun,thresholdRun],u.decisions++[.comparison comparison]⟩
  else
    let a:=approx (nativeExpressionFactorX residual t)
    let b:=approx (nativeExpressionFactorY residual t)
    ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
      u.expressions++[score,threshold]++a.expressions++b.expressions,
      u.comparisons+a.comparisons+b.comparisons+1,
      u.evaluations++[scoreRun,thresholdRun]++a.evaluations++b.evaluations,
      u.decisions++[.comparison comparison]++a.decisions++b.decisions⟩

theorem nativeTracedCorrection_word {m : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : NativePacketExpressionOracle → NativeArithmeticWordResult m)
    (plain : QuaternionOracle → List (Fin m))
    (ha : ∀ f,(approx f).word=plain (evaluateNativePacketOracle f)) (t : ℕ) (f : NativePacketExpressionOracle) :
    (nativeTracedCorrection entry inverseLabel approx t f).word=
      numericalCorrection (fun i => evaluateNativePacketOracle (entry i)) inverseLabel plain t
        (evaluateNativePacketOracle f) := by
  simp only [nativeTracedCorrection,numericalCorrection,ha,wordScalarLEProgram_value,
    NativeScalarExpression.wordRun_correct,nativeExpressionDistance_eval,nativeExpressionWord_eval,
    nativeExpressionPacketInverse_eval,nativeExpressionPacketMul_eval,nativeExpressionPacketOne_eval,
    nativeExpressionFactorX_eval,nativeExpressionFactorY_eval,residualSmall,decide_eq_true_eq,
    NativeScalarExpression.interpret,ScalarExpression.eval]
  split_ifs <;> rfl

theorem nativeTracedCorrection_evaluations {m : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : NativePacketExpressionOracle → NativeArithmeticWordResult m)
    (ha : ∀ f,(approx f).evaluations=(approx f).expressions.map NativeScalarExpression.wordRun)
    (t : ℕ) (f : NativePacketExpressionOracle) :
    (nativeTracedCorrection entry inverseLabel approx t f).evaluations=
      (nativeTracedCorrection entry inverseLabel approx t f).expressions.map NativeScalarExpression.wordRun := by
  unfold nativeTracedCorrection
  dsimp only
  split_ifs <;> simp only [ha,List.map_append,List.map_cons,List.map_nil]

/-- The double-correction recursion on native binary inputs. Selected
branches retain their one stored execution; score vectors are materialized. -/
def nativeTracedPairWord {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) :
    ℕ → NativePacketExpressionOracle → NativeArithmeticWordResult m
  | 0 => nativeTracedBase entry table
  | k+1 => nativeTracedCorrection entry inverseLabel
      (nativeTracedCorrection entry inverseLabel (nativeTracedPairWord entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem nativeTracedPairWord_word {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ)
    (f : NativePacketExpressionOracle) :
    (nativeTracedPairWord entry inverseLabel table k f).word=
      numericalPairWord (fun i => evaluateNativePacketOracle (entry i)) inverseLabel table k
        (evaluateNativePacketOracle f) := by
  induction k generalizing f with
  | zero => exact nativeTracedBase_word entry table f
  | succ k ih =>
    exact nativeTracedCorrection_word entry inverseLabel _ _
      (fun g => nativeTracedCorrection_word entry inverseLabel _ _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

theorem nativeTracedPairWord_evaluations {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ)
    (f : NativePacketExpressionOracle) :
    (nativeTracedPairWord entry inverseLabel table k f).evaluations=
      (nativeTracedPairWord entry inverseLabel table k f).expressions.map NativeScalarExpression.wordRun := by
  induction k generalizing f with
  | zero => exact nativeTracedBase_evaluations entry table f
  | succ k ih =>
    exact nativeTracedCorrection_evaluations entry inverseLabel _
      (fun g => nativeTracedCorrection_evaluations entry inverseLabel _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

end CircuitRecursion
