import CircuitNumerical.ListAssemblyPrograms

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

inductive InputListAssemblyTrace where
  | base
  | stopped : InputListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace → InputListAssemblyTrace
  | corrected : InputListAssemblyTrace → InputListAssemblyTrace → InputListAssemblyTrace →
      ListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace →
      ListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace → InputListAssemblyTrace

def InputListAssemblyTrace.actions : InputListAssemblyTrace → ℕ
  | .base => 0
  | .stopped u es ev ds => u.actions+es.actions+ev.actions+ds.actions
  | .corrected u a b ib ia w0 w1 es ev ds =>
      u.actions+a.actions+b.actions+ib.actions+ia.actions+w0.actions+w1.actions+es.actions+ev.actions+ds.actions

def InputListAssemblyTrace.inverseCalls : InputListAssemblyTrace → ℕ
  | .base => 0
  | .stopped u _ _ _ => u.inverseCalls
  | .corrected u a b ib ia _ _ _ _ _ => u.inverseCalls+a.inverseCalls+b.inverseCalls+ib.copies+ia.copies

structure AssembledInputWordResult (m : ℕ) where
  program : InputArithmeticWordResult m
  trace : InputListAssemblyTrace

/-- Only the three concrete retained-list concatenations execute here. -/
def assembleStoppedInput {m : ℕ} (u : AssembledInputWordResult m)
    (score threshold : InputScalarExpression m) (scoreRun thresholdRun : InputScalarEvaluation m)
    (comparison : WordScalarComparisonResult) : AssembledInputWordResult m :=
  let es:=listAppendProgram u.program.expressions [score,threshold]
  let ev:=listAppendProgram u.program.evaluations [scoreRun,thresholdRun]
  let ds:=listAppendProgram u.program.decisions [.comparison comparison]
  ⟨⟨u.program.word,es.value,u.program.comparisons+1,ev.value,ds.value⟩,
    .stopped u.trace es.trace ev.trace ds.trace⟩

/-- Each reverse-map and each list copy is an actual call stored once.
The trace is annotation data; its own allocation/arithmetic is separate. -/
def assembleCorrectedInput {m : ℕ} (inverseLabel : Fin m → Fin m)
    (u a b : AssembledInputWordResult m) (score threshold : InputScalarExpression m)
    (scoreRun thresholdRun : InputScalarEvaluation m) (comparison : WordScalarComparisonResult) : AssembledInputWordResult m :=
  let ib:=instructionInverseProgram inverseLabel b.program.word
  let ia:=instructionInverseProgram inverseLabel a.program.word
  let w0:=listAppendFourProgram u.program.word ib.value ia.value b.program.word
  let w1:=listAppendProgram w0.value a.program.word
  let es:=listAppendFourProgram u.program.expressions [score,threshold] a.program.expressions b.program.expressions
  let ev:=listAppendFourProgram u.program.evaluations [scoreRun,thresholdRun] a.program.evaluations b.program.evaluations
  let ds:=listAppendFourProgram u.program.decisions [.comparison comparison] a.program.decisions b.program.decisions
  ⟨⟨w1.value,es.value,u.program.comparisons+a.program.comparisons+b.program.comparisons+1,ev.value,ds.value⟩,
    .corrected u.trace a.trace b.trace ib.trace ia.trace w0.trace w1.trace es.trace ev.trace ds.trace⟩

theorem assembleStoppedInput_program {m : ℕ} (u : AssembledInputWordResult m)
    (score threshold : InputScalarExpression m) (scoreRun thresholdRun : InputScalarEvaluation m)
    (comparison : WordScalarComparisonResult) :
    (assembleStoppedInput u score threshold scoreRun thresholdRun comparison).program=
      ⟨u.program.word,u.program.expressions++[score,threshold],u.program.comparisons+1,
        u.program.evaluations++[scoreRun,thresholdRun],u.program.decisions++[.comparison comparison]⟩ := by
  simp only [assembleStoppedInput,listAppendProgram_value]

theorem assembleCorrectedInput_program {m : ℕ} (inverseLabel : Fin m → Fin m)
    (u a b : AssembledInputWordResult m) (score threshold : InputScalarExpression m)
    (scoreRun thresholdRun : InputScalarEvaluation m) (comparison : WordScalarComparisonResult) :
    (assembleCorrectedInput inverseLabel u a b score threshold scoreRun thresholdRun comparison).program=
      ⟨u.program.word++instructionInverse inverseLabel b.program.word++instructionInverse inverseLabel a.program.word++b.program.word++a.program.word,
        u.program.expressions++[score,threshold]++a.program.expressions++b.program.expressions,
        u.program.comparisons+a.program.comparisons+b.program.comparisons+1,
        u.program.evaluations++[scoreRun,thresholdRun]++a.program.evaluations++b.program.evaluations,
        u.program.decisions++[.comparison comparison]++a.program.decisions++b.program.decisions⟩ := by
  simp only [assembleCorrectedInput,listAppendFourProgram_value,listAppendProgram_value,instructionInverseProgram_value]

/-- This value program uses the list-copy backends above. Score evaluation
and Boolean decisions are the same stored operations as inputTracedCorrection. -/
def assembledInputCorrection {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → AssembledInputWordResult m) (t : ℕ)
    (f : InputPacketExpressionOracle m) : AssembledInputWordResult m :=
  let u:=approx f
  let residual:=inputExpressionPacketMul f (inputExpressionPacketInverse (inputExpressionWord entry u.program.word))
  let score:=inputExpressionDistance residual inputExpressionPacketOne (2*t+2)
  let threshold:=InputScalarExpression.stoppingThreshold t
  let scoreRun:=score.inputRun cache
  let thresholdRun:=threshold.inputRun cache
  let comparison:=wordScalarLEProgram scoreRun.numerical.value thresholdRun.numerical.value
  if comparison.le then assembleStoppedInput u score threshold scoreRun thresholdRun comparison else
    let a:=approx (inputExpressionFactorX residual t)
    let b:=approx (inputExpressionFactorY residual t)
    assembleCorrectedInput inverseLabel u a b score threshold scoreRun thresholdRun comparison

theorem assembledInputCorrection_program {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → AssembledInputWordResult m)
    (plain : InputPacketExpressionOracle m → InputArithmeticWordResult m)
    (ha : ∀ f,(approx f).program=plain f) (t : ℕ) (f : InputPacketExpressionOracle m) :
    (assembledInputCorrection cache entry inverseLabel approx t f).program=
      inputTracedCorrection cache entry inverseLabel plain t f := by
  unfold assembledInputCorrection inputTracedCorrection
  simp only [ha]
  split_ifs <;> simp only [assembleStoppedInput_program,assembleCorrectedInput_program,ha]

def assembledInputPairWord {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) : ℕ → InputPacketExpressionOracle m → AssembledInputWordResult m
  | 0,f => ⟨inputTracedBase cache entry table f,.base⟩
  | k+1,f => assembledInputCorrection cache entry inverseLabel
      (assembledInputCorrection cache entry inverseLabel (assembledInputPairWord cache entry inverseLabel table k)
        (numericalThreshold k)) (numericalThreshold k) f

theorem assembledInputPairWord_program {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m) :
    (assembledInputPairWord cache entry inverseLabel table k f).program=
      inputTracedPairWord cache entry inverseLabel table k f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    exact assembledInputCorrection_program cache entry inverseLabel _ _
      (fun g => assembledInputCorrection_program cache entry inverseLabel _ _ ih (numericalThreshold k) g)
      (numericalThreshold k) f

end CircuitRecursion
