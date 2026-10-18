import CircuitNumerical.InputCachePolynomial

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/-- A proof-side view of the already retained numerical records. It does
not re-run expressions or caches in the actual input-reference program. -/
def InputArithmeticWordResult.nativeView {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : NativeArithmeticWordResult m :=
  ⟨r.word,r.expressions.map (fun e => e.resolve cache),r.comparisons,
    r.evaluations.map InputScalarEvaluation.numerical,r.decisions⟩

theorem InputArithmeticWordResult.nativeView_word {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).word=r.word := rfl
theorem InputArithmeticWordResult.nativeView_expressions {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) :
    (r.nativeView cache).expressions=r.expressions.map (fun e => e.resolve cache) := rfl
theorem InputArithmeticWordResult.nativeView_comparisons {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).comparisons=r.comparisons := rfl
theorem InputArithmeticWordResult.nativeView_evaluations {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) :
    (r.nativeView cache).evaluations=r.evaluations.map InputScalarEvaluation.numerical := rfl
theorem InputArithmeticWordResult.nativeView_decisions {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).decisions=r.decisions := rfl

theorem inputTracedBase_nativeView {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (table : Fin (n+1) → List (Fin m))
    (f : InputPacketExpressionOracle m) :
    (inputTracedBase cache entry table f).nativeView cache=
      nativeTracedBase (fun i => resolveInputPacketOracle cache (entry i)) table (resolveInputPacketOracle cache f) := by
  simp only [inputTracedBase,InputArithmeticWordResult.nativeView,nativeTracedBase,inputVectorMapOfFn,
    List.Vector.toList_ofFn,List.map_ofFn,Function.comp_def,InputScalarExpression.inputRun_numerical,
    inputExpressionDistance_resolve,inputExpressionWord_resolve]


def InputScalarExpression.integerBitBudget {m P : ℕ} (e : InputScalarExpression m)
    (cache : NativeCacheEnvironment m P) : ℕ := (e.resolve cache).interpret.integerBitBudget
def InputScalarExpression.operations {m P : ℕ} (e : InputScalarExpression m)
    (cache : NativeCacheEnvironment m P) : ℕ := (e.resolve cache).interpret.operations
def InputArithmeticWordResult.integerBitBudget {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : ℕ := (r.expressions.map (fun e => e.integerBitBudget cache)).sum
def InputArithmeticWordResult.evaluationActions {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  (r.evaluations.map (fun run => run.numerical.trace.booleanActions)).sum
def InputArithmeticWordResult.decisionActions {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  (r.decisions.map WordDecisionTrace.actions).sum
def InputArithmeticWordResult.numericalActions {m : ℕ} (r : InputArithmeticWordResult m) : ℕ :=
  r.evaluationActions+r.decisionActions

theorem InputScalarExpression.inputRun_height {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) (B : ℕ) (h : e.integerBitBudget cache≤B) :
    IntegerScalarHeight (e.inputRun cache).numerical.value.decode B := by
  rw [InputScalarExpression.inputRun_numerical]
  exact NativeScalarExpression.wordRun_height (e.resolve cache) B h

theorem InputArithmeticWordResult.nativeView_budget {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).integerBitBudget=r.integerBitBudget cache := by
  simp only [InputArithmeticWordResult.nativeView,NativeArithmeticWordResult.integerBitBudget,
    InputArithmeticWordResult.integerBitBudget,InputScalarExpression.integerBitBudget,List.map_map,Function.comp_def,
    NativeScalarExpression.integerBitBudget]

theorem InputArithmeticWordResult.nativeView_operations {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).operations=r.operations cache := by
  simp only [InputArithmeticWordResult.nativeView,NativeArithmeticWordResult.operations,InputArithmeticWordResult.operations,
    NativeScalarExpression.operations,List.map_map,Function.comp_def]

theorem InputArithmeticWordResult.nativeView_evaluationActions {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) : (r.nativeView cache).evaluationActions=r.evaluationActions := by
  simp only [InputArithmeticWordResult.nativeView,NativeArithmeticWordResult.evaluationActions,
    InputArithmeticWordResult.evaluationActions,List.map_map,Function.comp_def]

theorem inputScalarExpressionList_length_le_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (es : List (InputScalarExpression m)) : es.length≤(es.map (fun e => e.operations cache)).sum := by
  have h:=nativeScalarExpressionList_length_le_operations (es.map (fun e => e.resolve cache))
  simpa only [List.length_map,List.map_map,Function.comp_def,InputScalarExpression.operations,NativeScalarExpression.operations] using h

theorem InputArithmeticWordResult.evaluationActions_bound {m P : ℕ} (r : InputArithmeticWordResult m)
    (cache : NativeCacheEnvironment m P) (hmatch : r.evaluations=r.expressions.map (fun e => e.inputRun cache))
    (B : ℕ) (hB : r.integerBitBudget cache≤B) : r.evaluationActions≤wordNodeBooleanBudget B*r.operations cache := by
  have hmatchView : (r.nativeView cache).evaluations=(r.nativeView cache).expressions.map NativeScalarExpression.wordRun := by
    simp only [InputArithmeticWordResult.nativeView,hmatch,List.map_map,Function.comp_def,InputScalarExpression.inputRun_numerical]
  have h:=NativeArithmeticWordResult.evaluationActions_bound (r.nativeView cache) hmatchView B (by
    rw [InputArithmeticWordResult.nativeView_budget]
    exact hB)
  simpa only [InputArithmeticWordResult.nativeView_evaluationActions,InputArithmeticWordResult.nativeView_operations] using h

theorem inputTracedPairWord_evaluationActions {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m) (B : ℕ)
    (hB : (inputTracedPairWord cache entry inverseLabel table k f).integerBitBudget cache≤B) :
    (inputTracedPairWord cache entry inverseLabel table k f).evaluationActions≤
      wordNodeBooleanBudget B*(inputTracedPairWord cache entry inverseLabel table k f).operations cache :=
  InputArithmeticWordResult.evaluationActions_bound _ cache (inputTracedPairWord_evaluations cache entry inverseLabel table k f) B hB

theorem inputTracedBase_decisionActions {m n P : ℕ} (cache : NativeCacheEnvironment m P) (entry : Fin m → InputPacketExpressionOracle m)
    (table : Fin (n+1) → List (Fin m)) (f : InputPacketExpressionOracle m) (B : ℕ)
    (hB : (inputTracedBase cache entry table f).integerBitBudget cache≤B) :
    (inputTracedBase cache entry table f).decisionActions≤wordDecisionBooleanBudget B*
      ((inputTracedBase cache entry table f).expressions.length+(inputTracedBase cache entry table f).comparisons) := by
  let scores:=List.Vector.ofFn (fun j => inputExpressionDistance f (inputExpressionWord entry (table j)) 20)
  let stored:=scores.map (fun e => e.inputRun cache)
  have hsum : (∑ i : Fin (n+1),(scores.get i).integerBitBudget cache)≤B := by
    simpa only [inputTracedBase,InputArithmeticWordResult.integerBitBudget,List.Vector.toList_ofFn,List.map_ofFn,
      List.sum_ofFn,Function.comp_apply,scores,List.Vector.get_ofFn] using hB
  have hi : ∀ i,(scores.get i).integerBitBudget cache≤B := by
    intro i
    exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores.get j).integerBitBudget cache))
      (Finset.mem_univ i)).trans hsum
  have hc:=wordMinimumProgram_height_actions n (stored.map (fun e => e.numerical.value)) B (by
    intro i
    simpa only [stored,List.Vector.get_map] using InputScalarExpression.inputRun_height cache (scores.get i) B (hi i))
  change (wordMinimumProgram n (stored.map (fun e => e.numerical.value))).trace.actions≤
    wordDecisionBooleanBudget B*(scores.toList.length+n)
  have hlen : scores.toList.length=n+1 := scores.2
  rw [hlen]
  dsimp only [wordDecisionBooleanBudget]
  nlinarith

theorem inputTracedCorrection_decisionActions {m P : ℕ} (cache : NativeCacheEnvironment m P) (entry : Fin m → InputPacketExpressionOracle m)
    (inverseLabel : Fin m → Fin m) (approx : InputPacketExpressionOracle m → InputArithmeticWordResult m)
    (ha : ∀ f B,(approx f).integerBitBudget cache≤B →
      (approx f).decisionActions≤wordDecisionBooleanBudget B*
        ((approx f).expressions.length+(approx f).comparisons))
    (t : ℕ) (f : InputPacketExpressionOracle m) (B : ℕ)
    (hB : (inputTracedCorrection cache entry inverseLabel approx t f).integerBitBudget cache≤B) :
    (inputTracedCorrection cache entry inverseLabel approx t f).decisionActions≤wordDecisionBooleanBudget B*
      ((inputTracedCorrection cache entry inverseLabel approx t f).expressions.length+
        (inputTracedCorrection cache entry inverseLabel approx t f).comparisons) := by
  let u:=approx f
  let residual:=inputExpressionPacketMul f (inputExpressionPacketInverse (inputExpressionWord entry u.word))
  let score:=inputExpressionDistance residual inputExpressionPacketOne (2*t+2)
  let threshold : InputScalarExpression m := .stoppingThreshold t
  let a:=approx (inputExpressionFactorX residual t)
  let b:=approx (inputExpressionFactorY residual t)
  let comparison:=wordScalarLEProgram (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value
  unfold inputTracedCorrection at hB ⊢
  dsimp only at hB ⊢
  split_ifs at hB ⊢
  · change ((u.expressions++[score,threshold]).map (fun e => e.integerBitBudget cache)).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.integerBitBudget cache≤B := by change (u.expressions.map (fun e => e.integerBitBudget cache)).sum≤B;omega
    have hs : score.integerBitBudget cache≤B := by omega
    have ht : threshold.integerBitBudget cache≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hc:=wordScalarLEProgram_height_actions (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value B
      (InputScalarExpression.inputRun_height cache score B hs) (InputScalarExpression.inputRun_height cache threshold B ht)
    simp only [InputArithmeticWordResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.expressions++[score,threshold]).length+(u.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi ⊢
    nlinarith
  · change ((u.expressions++[score,threshold]++a.expressions++b.expressions).map
        (fun e => e.integerBitBudget cache)).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.integerBitBudget cache≤B := by change (u.expressions.map (fun e => e.integerBitBudget cache)).sum≤B;omega
    have haB : a.integerBitBudget cache≤B := by change (a.expressions.map (fun e => e.integerBitBudget cache)).sum≤B;omega
    have hbB : b.integerBitBudget cache≤B := by change (b.expressions.map (fun e => e.integerBitBudget cache)).sum≤B;omega
    have hs : score.integerBitBudget cache≤B := by omega
    have ht : threshold.integerBitBudget cache≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hai : a.decisionActions≤wordDecisionBooleanBudget B*(a.expressions.length+a.comparisons) := ha _ B haB
    have hbi : b.decisionActions≤wordDecisionBooleanBudget B*(b.expressions.length+b.comparisons) := ha _ B hbB
    have hc:=wordScalarLEProgram_height_actions (score.inputRun cache).numerical.value (threshold.inputRun cache).numerical.value B
      (InputScalarExpression.inputRun_height cache score B hs) (InputScalarExpression.inputRun_height cache threshold B ht)
    simp only [InputArithmeticWordResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)+a.decisionActions+b.decisionActions≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.expressions++[score,threshold]++a.expressions++b.expressions).length+
      (u.comparisons+a.comparisons+b.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi hai hbi ⊢
    nlinarith

theorem inputTracedPairWord_decisionActions {m n P : ℕ} (cache : NativeCacheEnvironment m P) (entry : Fin m → InputPacketExpressionOracle m)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : InputPacketExpressionOracle m) (B : ℕ)
    (hB : (inputTracedPairWord cache entry inverseLabel table k f).integerBitBudget cache≤B) :
    (inputTracedPairWord cache entry inverseLabel table k f).decisionActions≤wordDecisionBooleanBudget B*
      ((inputTracedPairWord cache entry inverseLabel table k f).expressions.length+
        (inputTracedPairWord cache entry inverseLabel table k f).comparisons) := by
  induction k generalizing f B with
  | zero => exact inputTracedBase_decisionActions cache entry table f B hB
  | succ k ih =>
    exact inputTracedCorrection_decisionActions cache entry inverseLabel _
      (fun g B hg => inputTracedCorrection_decisionActions cache entry inverseLabel _ ih (numericalThreshold k) g B hg)
      (numericalThreshold k) f B hB

theorem inputTracedPairWord_numericalActions {m n P : ℕ} (cache : NativeCacheEnvironment m P) (entry : Fin m → InputPacketExpressionOracle m)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : InputPacketExpressionOracle m) (B : ℕ)
    (hB : (inputTracedPairWord cache entry inverseLabel table k f).integerBitBudget cache≤B) :
    (inputTracedPairWord cache entry inverseLabel table k f).numericalActions≤
      2*wordNodeBooleanBudget B*(inputTracedPairWord cache entry inverseLabel table k f).operations cache := by
  let r:=inputTracedPairWord cache entry inverseLabel table k f
  have he:=inputTracedPairWord_evaluationActions cache entry inverseLabel table k f B hB
  have hd:=inputTracedPairWord_decisionActions cache entry inverseLabel table k f B hB
  have hlen:=inputScalarExpressionList_length_le_operations cache r.expressions
  have hdec:=wordDecisionBooleanBudget_le B
  have hslots : r.expressions.length+r.comparisons≤r.operations cache :=
    Nat.add_le_add_right hlen _
  have hcost:=Nat.mul_le_mul hdec hslots
  change r.evaluationActions≤_ at he
  change r.decisionActions≤_ at hd
  change r.numericalActions≤_
  dsimp only [InputArithmeticWordResult.numericalActions]
  nlinarith

end CircuitRecursion
