import CircuitNumerical.InputListAssembly

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/-- List payload mass only. AST closure bodies and numeric bit payloads are
not traversed by the list-assembly routines. -/
def InputArithmeticWordResult.assemblyMass {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  r.word.length+r.expressions.length+r.evaluations.length+r.decisions.length+1

theorem InputArithmeticWordResult.assemblyMass_pos {m : ℕ} (r : InputArithmeticWordResult m) :
    1≤r.assemblyMass := by unfold InputArithmeticWordResult.assemblyMass;omega

theorem assembleStoppedInput_mass {m : ℕ} (u : AssembledInputWordResult m)
    (score threshold : InputScalarExpression m) (scoreRun thresholdRun : InputScalarEvaluation m)
    (comparison : WordScalarComparisonResult) :
    (assembleStoppedInput u score threshold scoreRun thresholdRun comparison).program.assemblyMass=u.program.assemblyMass+5 := by
  rw [assembleStoppedInput_program]
  simp only [InputArithmeticWordResult.assemblyMass,List.length_append,List.length_cons,List.length_nil]
  omega

theorem assembleCorrectedInput_mass {m : ℕ} (inverseLabel : Fin m → Fin m)
    (u a b : AssembledInputWordResult m) (score threshold : InputScalarExpression m)
    (scoreRun thresholdRun : InputScalarEvaluation m) (comparison : WordScalarComparisonResult) :
    (assembleCorrectedInput inverseLabel u a b score threshold scoreRun thresholdRun comparison).program.assemblyMass=
      u.program.assemblyMass+a.program.assemblyMass+b.program.assemblyMass+a.program.word.length+b.program.word.length+3 := by
  rw [assembleCorrectedInput_program]
  simp only [InputArithmeticWordResult.assemblyMass,List.length_append,List.length_cons,List.length_nil,
    instructionInverse,List.length_map,List.length_reverse]
  omega

theorem assembleStoppedInput_bounds {m : ℕ} (u : AssembledInputWordResult m)
    (score threshold : InputScalarExpression m) (scoreRun thresholdRun : InputScalarEvaluation m)
    (comparison : WordScalarComparisonResult) (M F : ℕ) (hM : 1≤M)
    (hu : u.program.assemblyMass≤M) (huf : u.trace.actions≤F) :
    (assembleStoppedInput u score threshold scoreRun thresholdRun comparison).program.assemblyMass≤8*M ∧
    (assembleStoppedInput u score threshold scoreRun thresholdRun comparison).trace.actions≤3*F+512*M := by
  constructor
  · rw [assembleStoppedInput_mass];omega
  · simp only [assembleStoppedInput,InputListAssemblyTrace.actions,listAppendProgram_actions]
    unfold InputArithmeticWordResult.assemblyMass at hu
    omega

theorem assembleCorrectedInput_bounds {m : ℕ} (inverseLabel : Fin m → Fin m)
    (u a b : AssembledInputWordResult m) (score threshold : InputScalarExpression m)
    (scoreRun thresholdRun : InputScalarEvaluation m) (comparison : WordScalarComparisonResult)
    (M F : ℕ) (_hM : 1≤M)
    (hu : u.program.assemblyMass≤M) (ha : a.program.assemblyMass≤M) (hb : b.program.assemblyMass≤M)
    (huf : u.trace.actions≤F) (haf : a.trace.actions≤F) (hbf : b.trace.actions≤F) :
    (assembleCorrectedInput inverseLabel u a b score threshold scoreRun thresholdRun comparison).program.assemblyMass≤8*M ∧
    (assembleCorrectedInput inverseLabel u a b score threshold scoreRun thresholdRun comparison).trace.actions≤3*F+512*M := by
  have hua:=hu;have haa:=ha;have hba:=hb
  unfold InputArithmeticWordResult.assemblyMass at hua haa hba
  constructor
  · rw [assembleCorrectedInput_mass]
    omega
  · simp only [assembleCorrectedInput,InputListAssemblyTrace.actions,instructionInverseProgram_actions,
      listAppendFourProgram_actions_exact,listAppendProgram_actions,listAppendFourProgram_value,
      instructionInverseProgram_value,instructionInverse,List.length_map,List.length_reverse,List.length_append,
      List.length_cons,List.length_nil]
    omega

theorem assembledInputCorrection_bounds {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (approx : InputPacketExpressionOracle m → AssembledInputWordResult m) (t : ℕ)
    (f : InputPacketExpressionOracle m) (M F : ℕ) (hM : 1≤M)
    (ha : ∀ g,(approx g).program.assemblyMass≤M ∧ (approx g).trace.actions≤F) :
    (assembledInputCorrection cache entry inverseLabel approx t f).program.assemblyMass≤8*M ∧
    (assembledInputCorrection cache entry inverseLabel approx t f).trace.actions≤3*F+512*M := by
  unfold assembledInputCorrection
  dsimp only
  split_ifs
  · exact assembleStoppedInput_bounds _ _ _ _ _ _ M F hM (ha f).1 (ha f).2
  · exact assembleCorrectedInput_bounds _ _ _ _ _ _ _ _ _ M F hM
      (ha f).1 (ha _).1 (ha _).1 (ha f).2 (ha _).2 (ha _).2

theorem inputTracedBase_assemblyMass {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (table : Fin (n+1) → List (Fin m))
    (L : ℕ) (hL : ∀ j,(table j).length≤L) (f : InputPacketExpressionOracle m) :
    (inputTracedBase cache entry table f).assemblyMass≤L+2*(n+1)+2 := by
  let scores:=List.Vector.ofFn (fun j => inputExpressionDistance f (inputExpressionWord entry (table j)) 20)
  let stored:=scores.map (fun e => e.inputRun cache)
  let minimum:=wordMinimumProgram n (stored.map (fun x => x.numerical.value))
  change (table minimum.index).length+scores.toList.length+stored.toList.length+1+1≤_
  have hs : scores.toList.length=n+1 := scores.2
  have ht : stored.toList.length=n+1 := stored.2
  rw [hs,ht]
  have h:=hL minimum.index
  omega

theorem InputListAssemblyTrace.inverseCalls_le_actions (t : InputListAssemblyTrace) : t.inverseCalls≤t.actions := by
  induction t with
  | base => exact le_refl 0
  | stopped u es ev ds ih =>
    simp only [InputListAssemblyTrace.inverseCalls,InputListAssemblyTrace.actions]
    omega
  | corrected u a b ib ia w0 w1 es ev ds hu ha hb =>
    have hib:=ib.copies_le_actions
    have hia:=ia.copies_le_actions
    simp only [InputListAssemblyTrace.inverseCalls,InputListAssemblyTrace.actions]
    omega

/-- A joint bound for actual retained payload-list sizes and concrete
copy/reverse-map traces. It makes no assumption about numerical input sizes. -/
theorem assembledInputPairWord_bounds {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (k : ℕ) (f : InputPacketExpressionOracle m) :
    (assembledInputPairWord cache entry inverseLabel table k f).program.assemblyMass≤8192^k*(L+2*(n+1)+2) ∧
    (assembledInputPairWord cache entry inverseLabel table k f).trace.actions≤8192^k*(L+2*(n+1)+2) := by
  induction k generalizing f with
  | zero =>
    constructor
    · simpa only [assembledInputPairWord,pow_zero,one_mul] using inputTracedBase_assemblyMass cache entry table L hL f
    · simp only [assembledInputPairWord,InputListAssemblyTrace.actions,pow_zero,one_mul,Nat.zero_le]
  | succ k ih =>
    let M:=8192^k*(L+2*(n+1)+2)
    have hM : 1≤M := by
      have hp : 1≤8192^k := Nat.one_le_pow _ _ (by decide)
      dsimp only [M]
      nlinarith
    have hin : ∀ g,
        (assembledInputCorrection cache entry inverseLabel (assembledInputPairWord cache entry inverseLabel table k)
          (numericalThreshold k) g).program.assemblyMass≤8*M ∧
        (assembledInputCorrection cache entry inverseLabel (assembledInputPairWord cache entry inverseLabel table k)
          (numericalThreshold k) g).trace.actions≤3*M+512*M :=
      fun g => assembledInputCorrection_bounds cache entry inverseLabel _ _ g M M hM ih
    have hout:=assembledInputCorrection_bounds cache entry inverseLabel _ (numericalThreshold k) f
      (8*M) (3*M+512*M) (by omega) hin
    have hm:=hout.1
    have hf:=hout.2
    change (assembledInputPairWord cache entry inverseLabel table (k+1) f).program.assemblyMass≤8*(8*M) at hm
    change (assembledInputPairWord cache entry inverseLabel table (k+1) f).trace.actions≤3*(3*M+512*M)+512*(8*M) at hf
    have he : 8192^(k+1)*(L+2*(n+1)+2)=8192*M := by
      dsimp only [M]
      rw [pow_succ]
      ring
    rw [he]
    constructor <;> omega

end CircuitRecursion
