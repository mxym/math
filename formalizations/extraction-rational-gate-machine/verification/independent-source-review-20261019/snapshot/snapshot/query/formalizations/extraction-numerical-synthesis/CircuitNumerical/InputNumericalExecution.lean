import CircuitNumerical.InputCacheOracles

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure InputArithmeticWordResult (m : ℕ) where
  word : List (Fin m)
  expressions : List (InputScalarExpression m)
  comparisons : ℕ
  evaluations : List (InputScalarEvaluation m)
  decisions : List WordDecisionTrace

def inputTracedBase {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (table : Fin (n+1) → List (Fin m))
    (f : InputPacketExpressionOracle m) : InputArithmeticWordResult m :=
  let scores:=List.Vector.ofFn (fun j => inputExpressionDistance f (inputExpressionWord entry (table j)) 20)
  let stored:=scores.map (fun e => e.inputRun cache)
  let minimum:=wordMinimumProgram n (stored.map (fun x => x.numerical.value))
  ⟨table minimum.index,scores.toList,n,stored.toList,[.minimum minimum.trace]⟩

theorem inputTracedBase_word {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (table : Fin (n+1) → List (Fin m))
    (f : InputPacketExpressionOracle m) :
    (inputTracedBase cache entry table f).word=fixedNetWord
      (fun i => evaluateNativePacketOracle (resolveInputPacketOracle cache (entry i))) table
      (evaluateNativePacketOracle (resolveInputPacketOracle cache f)) := by
  simp only [inputTracedBase,wordMinimumProgram_index,integerMinIndex_eq,List.Vector.get_map,List.Vector.get_ofFn,
    InputScalarExpression.inputRun_numerical,NativeScalarExpression.wordRun_correct,inputExpressionDistance_resolve,
    inputExpressionWord_resolve,nativeExpressionDistance_eval,nativeExpressionWord_eval,fixedNetWord]
  congr 1
  congr 1
  funext i
  rw [List.Vector.get_ofFn]

theorem inputTracedBase_evaluations {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (table : Fin (n+1) → List (Fin m))
    (f : InputPacketExpressionOracle m) :
    (inputTracedBase cache entry table f).evaluations=
      (inputTracedBase cache entry table f).expressions.map (fun e => e.inputRun cache) := by rfl

/-- Input references remain symbolic during factor construction. Actual
cache reads occur inside these one-time stored score evaluations. -/
def inputTracedCorrection {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → InputArithmeticWordResult m) (t : ℕ)
    (f : InputPacketExpressionOracle m) : InputArithmeticWordResult m :=
  let u:=approx f
  let residual:=inputExpressionPacketMul f (inputExpressionPacketInverse (inputExpressionWord entry u.word))
  let score:=inputExpressionDistance residual inputExpressionPacketOne (2*t+2)
  let threshold:=InputScalarExpression.stoppingThreshold t
  let scoreRun:=score.inputRun cache
  let thresholdRun:=threshold.inputRun cache
  let comparison:=wordScalarLEProgram scoreRun.numerical.value thresholdRun.numerical.value
  if comparison.le then
    ⟨u.word,u.expressions++[score,threshold],u.comparisons+1,
      u.evaluations++[scoreRun,thresholdRun],u.decisions++[.comparison comparison]⟩
  else
    let a:=approx (inputExpressionFactorX residual t)
    let b:=approx (inputExpressionFactorY residual t)
    ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
      u.expressions++[score,threshold]++a.expressions++b.expressions,u.comparisons+a.comparisons+b.comparisons+1,
      u.evaluations++[scoreRun,thresholdRun]++a.evaluations++b.evaluations,
      u.decisions++[.comparison comparison]++a.decisions++b.decisions⟩

theorem inputTracedCorrection_word {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → InputArithmeticWordResult m)
    (plain : QuaternionOracle → List (Fin m))
    (ha : ∀ f,(approx f).word=plain (evaluateNativePacketOracle (resolveInputPacketOracle cache f)))
    (t : ℕ) (f : InputPacketExpressionOracle m) :
    (inputTracedCorrection cache entry inverseLabel approx t f).word=
      numericalCorrection (fun i => evaluateNativePacketOracle (resolveInputPacketOracle cache (entry i)))
        inverseLabel plain t (evaluateNativePacketOracle (resolveInputPacketOracle cache f)) := by
  simp only [inputTracedCorrection,numericalCorrection,ha,wordScalarLEProgram_value,
    InputScalarExpression.inputRun_numerical,NativeScalarExpression.wordRun_correct,inputExpressionDistance_resolve,
    inputExpressionWord_resolve,inputExpressionPacketMul_resolve,inputExpressionPacketInverse_resolve,
    inputExpressionPacketOne_resolve,inputExpressionFactorX_resolve,inputExpressionFactorY_resolve,
    nativeExpressionDistance_eval,nativeExpressionWord_eval,nativeExpressionPacketMul_eval,nativeExpressionPacketInverse_eval,
    nativeExpressionPacketOne_eval,nativeExpressionFactorX_eval,nativeExpressionFactorY_eval,
    residualSmall,decide_eq_true_eq,InputScalarExpression.resolve,NativeScalarExpression.interpret,ScalarExpression.eval]
  split_ifs <;> rfl

theorem inputTracedCorrection_evaluations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → InputArithmeticWordResult m)
    (ha : ∀ f,(approx f).evaluations=(approx f).expressions.map (fun e => e.inputRun cache))
    (t : ℕ) (f : InputPacketExpressionOracle m) :
    (inputTracedCorrection cache entry inverseLabel approx t f).evaluations=
      (inputTracedCorrection cache entry inverseLabel approx t f).expressions.map (fun e => e.inputRun cache) := by
  unfold inputTracedCorrection
  dsimp only
  split_ifs <;> simp only [ha,List.map_append,List.map_cons,List.map_nil]

def inputTracedPairWord {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) : ℕ → InputPacketExpressionOracle m → InputArithmeticWordResult m
  | 0 => inputTracedBase cache entry table
  | k+1 => inputTracedCorrection cache entry inverseLabel
      (inputTracedCorrection cache entry inverseLabel (inputTracedPairWord cache entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k)

theorem inputTracedPairWord_word {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m) :
    (inputTracedPairWord cache entry inverseLabel table k f).word=
      numericalPairWord (fun i => evaluateNativePacketOracle (resolveInputPacketOracle cache (entry i)))
        inverseLabel table k (evaluateNativePacketOracle (resolveInputPacketOracle cache f)) := by
  induction k generalizing f with
  | zero => exact inputTracedBase_word cache entry table f
  | succ k ih =>
    exact inputTracedCorrection_word cache entry inverseLabel _ _
      (fun g => inputTracedCorrection_word cache entry inverseLabel _ _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

theorem inputTracedPairWord_evaluations {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m) :
    (inputTracedPairWord cache entry inverseLabel table k f).evaluations=
      (inputTracedPairWord cache entry inverseLabel table k f).expressions.map (fun e => e.inputRun cache) := by
  induction k generalizing f with
  | zero => exact inputTracedBase_evaluations cache entry table f
  | succ k ih =>
    exact inputTracedCorrection_evaluations cache entry inverseLabel _
      (fun g => inputTracedCorrection_evaluations cache entry inverseLabel _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

def InputArithmeticWordResult.operations {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : ℕ :=
  (r.expressions.map (fun e => (e.resolve cache).interpret.operations)).sum+r.comparisons

def InputArithmeticWordResult.readActions {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  (r.evaluations.map (fun e => nativeCacheReadActions e.reads)).sum

theorem InputArithmeticWordResult.readActions_bound {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P)
    (hmatch : r.evaluations=r.expressions.map (fun e => e.inputRun cache)) :
    r.readActions≤4*(m+P+5)*r.operations cache := by
  have hs : (r.expressions.map (fun e => nativeCacheReadActions (e.inputRun cache).reads)).sum≤
      4*(m+P+5)*(r.expressions.map (fun e => (e.resolve cache).interpret.operations)).sum := by
    induction r.expressions with
    | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
    | cons e es ih =>
      have he:=InputScalarExpression.inputRun_readActions_operations cache e
      simp only [List.map_cons,List.sum_cons,Nat.mul_add]
      simpa only [Nat.mul_add] using Nat.add_le_add he ih
  simp only [InputArithmeticWordResult.readActions,hmatch,List.map_map,Function.comp_apply]
  exact hs.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

theorem inputTracedPairWord_readActions {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m) :
    (inputTracedPairWord cache entry inverseLabel table k f).readActions≤
      4*(m+P+5)*(inputTracedPairWord cache entry inverseLabel table k f).operations cache :=
  InputArithmeticWordResult.readActions_bound _ cache (inputTracedPairWord_evaluations cache entry inverseLabel table k f)

end CircuitRecursion
