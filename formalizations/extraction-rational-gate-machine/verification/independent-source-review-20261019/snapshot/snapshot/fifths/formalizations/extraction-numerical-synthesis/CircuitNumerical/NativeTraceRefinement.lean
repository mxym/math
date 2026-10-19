import CircuitNumerical.NativeFactorRefinement
import Mathlib.Data.List.Forall2

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

structure NativeArithmeticRefines {m : ℕ} (r : NativeArithmeticWordResult m) (R : ArithmeticWordResult m) : Prop where
  word_eq : r.word=R.word
  expressions : List.Forall₂ NativeScalarRefines r.expressions R.expressions
  comparisons_eq : r.comparisons=R.comparisons

theorem nativeScalarList_refines_budget {es : List NativeScalarExpression} {Es : List ScalarExpression}
    (h : List.Forall₂ NativeScalarRefines es Es) :
    (es.map NativeScalarExpression.integerBitBudget).sum≤20*(Es.map ScalarExpression.integerBitBudget).sum := by
  induction h with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons he ht ih =>
    have hb:=he.budget_le
    simp only [List.map_cons,List.sum_cons,NativeScalarExpression.integerBitBudget]
    omega

theorem nativeScalarList_refines_operations {es : List NativeScalarExpression} {Es : List ScalarExpression}
    (h : List.Forall₂ NativeScalarRefines es Es) :
    (es.map NativeScalarExpression.operations).sum≤20*(Es.map ScalarExpression.operations).sum := by
  induction h with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons he ht ih =>
    have hb:=he.operations_le
    simp only [List.map_cons,List.sum_cons,NativeScalarExpression.operations]
    omega

theorem NativeArithmeticRefines.budget_le {m : ℕ} {r : NativeArithmeticWordResult m} {R : ArithmeticWordResult m}
    (h : NativeArithmeticRefines r R) : r.integerBitBudget≤20*R.integerBitBudget :=
  nativeScalarList_refines_budget h.expressions

theorem NativeArithmeticRefines.operations_le {m : ℕ} {r : NativeArithmeticWordResult m} {R : ArithmeticWordResult m}
    (h : NativeArithmeticRefines r R) : r.operations≤20*R.operations := by
  have hb:=nativeScalarList_refines_operations h.expressions
  simp only [NativeArithmeticWordResult.operations,ArithmeticWordResult.operations,h.comparisons_eq]
  omega

theorem nativeTracedBase_refines {m n : ℕ} {entry : Fin m → NativePacketExpressionOracle}
    {E : Fin m → PacketExpressionOracle} (he : ∀ i,NativePacketOracleRefines (entry i) (E i))
    (table : Fin (n+1) → List (Fin m)) {f : NativePacketExpressionOracle} {F : PacketExpressionOracle}
    (hf : NativePacketOracleRefines f F) : NativeArithmeticRefines (nativeTracedBase entry table f) (tracedBase E table F) := by
  constructor
  · rw [nativeTracedBase_word,tracedBase_word,hf.eval_eq]
    have hev : (fun i => evaluateNativePacketOracle (entry i))=(fun i => evaluatePacketOracle (E i)) :=
      funext (fun i => (he i).eval_eq)
    rw [hev]
  · let scores:=List.Vector.ofFn (fun j => nativeExpressionDistance f (nativeExpressionWord entry (table j)) 20)
    let Scores:=List.Vector.ofFn (fun j => expressionDistance F (expressionWord E (table j)) 20)
    change List.Forall₂ NativeScalarRefines scores.toList Scores.toList
    apply List.forall₂_of_length_eq_of_get
    · exact scores.2.trans Scores.2.symm
    · intro i hi hI
      have hi' : i<n+1 := by
        have hlen : scores.toList.length=n+1 := scores.2
        omega
      change NativeScalarRefines (scores.get ⟨i,hi'⟩) (Scores.get ⟨i,hi'⟩)
      simp only [scores,Scores,List.Vector.get_ofFn]
      exact nativeExpressionDistance_refines hf (nativeExpressionWord_refines he _) 20
  · rfl

theorem nativeTracedCorrection_refines {m : ℕ} {entry : Fin m → NativePacketExpressionOracle}
    {E : Fin m → PacketExpressionOracle} (he : ∀ i,NativePacketOracleRefines (entry i) (E i))
    (inverseLabel : Fin m → Fin m) (approx : NativePacketExpressionOracle → NativeArithmeticWordResult m)
    (Approx : PacketExpressionOracle → ArithmeticWordResult m)
    (ha : ∀ f F,NativePacketOracleRefines f F → NativeArithmeticRefines (approx f) (Approx F))
    (t : ℕ) {f : NativePacketExpressionOracle} {F : PacketExpressionOracle} (hf : NativePacketOracleRefines f F) :
    NativeArithmeticRefines (nativeTracedCorrection entry inverseLabel approx t f)
      (tracedCorrection E inverseLabel Approx t F) := by
  let u:=approx f
  let U:=Approx F
  have hu : NativeArithmeticRefines u U := ha f F hf
  let residual:=nativeExpressionPacketMul f (nativeExpressionPacketInverse (nativeExpressionWord entry u.word))
  let Residual:=expressionPacketMul F (expressionPacketInverse (expressionWord E U.word))
  have hr : NativePacketOracleRefines residual Residual := by
    dsimp only [residual,Residual]
    rw [←hu.word_eq]
    exact nativeExpressionPacketMul_refines hf (nativeExpressionPacketInverse_refines (nativeExpressionWord_refines he _))
  let score:=nativeExpressionDistance residual nativeExpressionPacketOne (2*t+2)
  let Score:=expressionDistance Residual expressionPacketOne (2*t+2)
  have hs : NativeScalarRefines score Score := nativeExpressionDistance_refines hr nativePacketOne_refines (2*t+2)
  let threshold:=NativeScalarExpression.stoppingThreshold t
  let Threshold:=ScalarExpression.stoppingThreshold t
  have ht : NativeScalarRefines threshold Threshold := NativeScalarRefines.threshold t
  let a:=approx (nativeExpressionFactorX residual t)
  let b:=approx (nativeExpressionFactorY residual t)
  let A:=Approx (expressionFactorX Residual t)
  let B:=Approx (expressionFactorY Residual t)
  have hA : NativeArithmeticRefines a A := ha _ _ (nativeExpressionFactorX_refines hr t)
  have hB : NativeArithmeticRefines b B := ha _ _ (nativeExpressionFactorY_refines hr t)
  have hcompare : (wordScalarLEProgram score.wordRun.value threshold.wordRun.value).le=
      decide (Score.eval≤Threshold.eval) := by
    apply Bool.eq_iff_iff.mpr
    simp only [wordScalarLEProgram_value,decide_eq_true_eq,NativeScalarExpression.wordRun_correct,
      hs.eval_eq,ht.eval_eq]
  change NativeArithmeticRefines
    (if (wordScalarLEProgram score.wordRun.value threshold.wordRun.value).le then
      ⟨u.word,u.expressions++[score,threshold],u.comparisons+1,
        u.evaluations++[score.wordRun,threshold.wordRun],u.decisions++[.comparison (wordScalarLEProgram score.wordRun.value threshold.wordRun.value)]⟩
      else ⟨u.word++instructionInverse inverseLabel b.word++instructionInverse inverseLabel a.word++b.word++a.word,
        u.expressions++[score,threshold]++a.expressions++b.expressions,u.comparisons+a.comparisons+b.comparisons+1,
        u.evaluations++[score.wordRun,threshold.wordRun]++a.evaluations++b.evaluations,
        u.decisions++[.comparison (wordScalarLEProgram score.wordRun.value threshold.wordRun.value)]++a.decisions++b.decisions⟩)
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

theorem nativeTracedPairWord_refines {m n : ℕ} {entry : Fin m → NativePacketExpressionOracle}
    {E : Fin m → PacketExpressionOracle} (he : ∀ i,NativePacketOracleRefines (entry i) (E i))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (k : ℕ)
    {f : NativePacketExpressionOracle} {F : PacketExpressionOracle} (hf : NativePacketOracleRefines f F) :
    NativeArithmeticRefines (nativeTracedPairWord entry inverseLabel table k f)
      (tracedPairWord E inverseLabel table k F) := by
  induction k generalizing f F with
  | zero => exact nativeTracedBase_refines he table hf
  | succ k ih =>
    exact nativeTracedCorrection_refines he inverseLabel _ _
      (fun g G hg => nativeTracedCorrection_refines he inverseLabel _ _ (fun h H hh => ih hh) (numericalThreshold k) hg)
      (numericalThreshold k) hf

end CircuitRecursion
