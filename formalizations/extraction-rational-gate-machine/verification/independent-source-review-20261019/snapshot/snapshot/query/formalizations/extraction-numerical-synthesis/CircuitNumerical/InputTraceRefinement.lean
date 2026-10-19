import CircuitNumerical.InputNumericalExecution
import Mathlib.Data.List.Forall2

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure InputArithmeticRefines {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (r : InputArithmeticWordResult m) (R : ArithmeticWordResult m) : Prop where
  word_eq : r.word=R.word
  expressions : List.Forall₂ (fun e E => NativeScalarRefines (e.resolve cache) E) r.expressions R.expressions
  comparisons_eq : r.comparisons=R.comparisons

theorem inputScalarList_refines_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    {es : List (InputScalarExpression m)} {Es : List ScalarExpression}
    (h : List.Forall₂ (fun e E => NativeScalarRefines (e.resolve cache) E) es Es) :
    (es.map (fun e => (e.resolve cache).interpret.operations)).sum≤20*(Es.map ScalarExpression.operations).sum := by
  induction h with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons he ht ih =>
    have hb:=he.operations_le
    simp only [List.map_cons,List.sum_cons]
    omega

theorem InputArithmeticRefines.operations_le {m P : ℕ} {cache : NativeCacheEnvironment m P}
    {r : InputArithmeticWordResult m} {R : ArithmeticWordResult m} (h : InputArithmeticRefines cache r R) :
    r.operations cache≤20*R.operations := by
  have hb:=inputScalarList_refines_operations cache h.expressions
  simp only [InputArithmeticWordResult.operations,ArithmeticWordResult.operations,h.comparisons_eq]
  omega

theorem inputTracedBase_refines {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    {entry : Fin m → InputPacketExpressionOracle m} {E : Fin m → PacketExpressionOracle}
    (he : ∀ i,NativePacketOracleRefines (resolveInputPacketOracle cache (entry i)) (E i))
    (table : Fin (n+1) → List (Fin m)) {f : InputPacketExpressionOracle m} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines (resolveInputPacketOracle cache f) F) :
    InputArithmeticRefines cache (inputTracedBase cache entry table f) (tracedBase E table F) := by
  constructor
  · rw [inputTracedBase_word,tracedBase_word,hf.eval_eq]
    have hev : (fun i => evaluateNativePacketOracle (resolveInputPacketOracle cache (entry i)))=
        (fun i => evaluatePacketOracle (E i)) := funext (fun i => (he i).eval_eq)
    rw [hev]
  · let scores:=List.Vector.ofFn (fun j => inputExpressionDistance f (inputExpressionWord entry (table j)) 20)
    let Scores:=List.Vector.ofFn (fun j => expressionDistance F (expressionWord E (table j)) 20)
    change List.Forall₂ (fun e E => NativeScalarRefines (e.resolve cache) E) scores.toList Scores.toList
    apply List.forall₂_of_length_eq_of_get
    · exact scores.2.trans Scores.2.symm
    · intro i hi hI
      have hi' : i<n+1 := by
        have hlen : scores.toList.length=n+1 := scores.2
        omega
      change NativeScalarRefines ((scores.get ⟨i,hi'⟩).resolve cache) (Scores.get ⟨i,hi'⟩)
      simp only [scores,Scores,List.Vector.get_ofFn,inputExpressionDistance_resolve,inputExpressionWord_resolve]
      exact nativeExpressionDistance_refines hf (nativeExpressionWord_refines he _) 20
  · rfl

theorem inputTracedCorrection_refines {m P : ℕ} (cache : NativeCacheEnvironment m P)
    {entry : Fin m → InputPacketExpressionOracle m} {E : Fin m → PacketExpressionOracle}
    (he : ∀ i,NativePacketOracleRefines (resolveInputPacketOracle cache (entry i)) (E i))
    (inverseLabel : Fin m → Fin m) (approx : InputPacketExpressionOracle m → InputArithmeticWordResult m)
    (Approx : PacketExpressionOracle → ArithmeticWordResult m)
    (ha : ∀ f F,NativePacketOracleRefines (resolveInputPacketOracle cache f) F →
      InputArithmeticRefines cache (approx f) (Approx F))
    (t : ℕ) {f : InputPacketExpressionOracle m} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines (resolveInputPacketOracle cache f) F) :
    InputArithmeticRefines cache (inputTracedCorrection cache entry inverseLabel approx t f)
      (tracedCorrection E inverseLabel Approx t F) := by
  let u:=approx f
  let U:=Approx F
  have hu : InputArithmeticRefines cache u U := ha f F hf
  let residual:=inputExpressionPacketMul f (inputExpressionPacketInverse (inputExpressionWord entry u.word))
  let Residual:=expressionPacketMul F (expressionPacketInverse (expressionWord E U.word))
  have hr : NativePacketOracleRefines (resolveInputPacketOracle cache residual) Residual := by
    dsimp only [residual,Residual]
    rw [inputExpressionPacketMul_resolve,inputExpressionPacketInverse_resolve,inputExpressionWord_resolve,←hu.word_eq]
    exact nativeExpressionPacketMul_refines hf (nativeExpressionPacketInverse_refines (nativeExpressionWord_refines he _))
  let score:=inputExpressionDistance residual inputExpressionPacketOne (2*t+2)
  let Score:=expressionDistance Residual expressionPacketOne (2*t+2)
  have hs : NativeScalarRefines (score.resolve cache) Score := by
    dsimp only [score]
    rw [inputExpressionDistance_resolve,inputExpressionPacketOne_resolve]
    exact nativeExpressionDistance_refines hr nativePacketOne_refines (2*t+2)
  let threshold : InputScalarExpression m := .stoppingThreshold t
  let Threshold:=ScalarExpression.stoppingThreshold t
  have ht : NativeScalarRefines (threshold.resolve cache) Threshold := NativeScalarRefines.threshold t
  let a:=approx (inputExpressionFactorX residual t)
  let b:=approx (inputExpressionFactorY residual t)
  let A:=Approx (expressionFactorX Residual t)
  let B:=Approx (expressionFactorY Residual t)
  have hA : InputArithmeticRefines cache a A := ha _ _ (by
    rw [inputExpressionFactorX_resolve]
    exact nativeExpressionFactorX_refines hr t)
  have hB : InputArithmeticRefines cache b B := ha _ _ (by
    rw [inputExpressionFactorY_resolve]
    exact nativeExpressionFactorY_refines hr t)
  have hcompare : (wordScalarLEProgram (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value).le=
      decide (Score.eval≤Threshold.eval) := by
    apply Bool.eq_iff_iff.mpr
    simp only [wordScalarLEProgram_value,decide_eq_true_eq,InputScalarExpression.inputRun_numerical,
      NativeScalarExpression.wordRun_correct,hs.eval_eq,ht.eval_eq]
  change InputArithmeticRefines cache
    (if (wordScalarLEProgram (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value).le then
      ⟨u.word,u.expressions++[score,threshold],u.comparisons+1,
        u.evaluations++[score.inputRun cache,threshold.inputRun cache],
        u.decisions++[.comparison (wordScalarLEProgram (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value)]⟩
      else ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
        u.expressions++[score,threshold]++a.expressions++b.expressions,u.comparisons+a.comparisons+b.comparisons+1,
        u.evaluations++[score.inputRun cache,threshold.inputRun cache]++a.evaluations++b.evaluations,
        u.decisions++[.comparison (wordScalarLEProgram (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value)]++a.decisions++b.decisions⟩)
    (if Score.eval≤Threshold.eval then ⟨U.word,U.expressions++[Score,Threshold],U.comparisons+1⟩ else
      ⟨U.word++instructionInverse inverseLabel B.word++instructionInverse inverseLabel A.word++B.word++A.word,
        U.expressions++[Score,Threshold]++A.expressions++B.expressions,U.comparisons+A.comparisons+B.comparisons+1⟩)
  rw [hcompare]
  simp only [decide_eq_true_eq]
  split_ifs
  · exact ⟨hu.word_eq,List.rel_append hu.expressions (.cons hs (.cons ht .nil)),congrArg (fun n => n+1) hu.comparisons_eq⟩
  · constructor
    · simp only [hu.word_eq,hA.word_eq,hB.word_eq]
    · exact List.rel_append (List.rel_append (List.rel_append hu.expressions (.cons hs (.cons ht .nil))) hA.expressions) hB.expressions
    · simp only [hu.comparisons_eq,hA.comparisons_eq,hB.comparisons_eq]

theorem inputTracedPairWord_refines {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    {entry : Fin m → InputPacketExpressionOracle m} {E : Fin m → PacketExpressionOracle}
    (he : ∀ i,NativePacketOracleRefines (resolveInputPacketOracle cache (entry i)) (E i))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ)
    {f : InputPacketExpressionOracle m} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines (resolveInputPacketOracle cache f) F) :
    InputArithmeticRefines cache (inputTracedPairWord cache entry inverseLabel table k f) (tracedPairWord E inverseLabel table k F) := by
  induction k generalizing f F with
  | zero => exact inputTracedBase_refines cache he table hf
  | succ k ih =>
    exact inputTracedCorrection_refines cache he inverseLabel _ _
      (fun g G hg => inputTracedCorrection_refines cache he inverseLabel _ _ (fun h H hh => ih hh) (numericalThreshold k) hg)
      (numericalThreshold k) hf

end CircuitRecursion
