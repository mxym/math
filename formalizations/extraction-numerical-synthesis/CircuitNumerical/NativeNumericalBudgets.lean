import CircuitNumerical.NativeCachedSynthesis

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

/- These conservative budgets belong to proof/accounting semantics only.
The native value program never evaluates the interpretation. -/
def NativeScalarExpression.integerBitBudget (e : NativeScalarExpression) : ℕ := e.interpret.integerBitBudget
def NativeScalarExpression.operations (e : NativeScalarExpression) : ℕ := e.interpret.operations
def NativeArithmeticWordResult.integerBitBudget {m : ℕ} (r : NativeArithmeticWordResult m) : ℕ :=
  (r.expressions.map NativeScalarExpression.integerBitBudget).sum
def NativeArithmeticWordResult.operations {m : ℕ} (r : NativeArithmeticWordResult m) : ℕ :=
  (r.expressions.map NativeScalarExpression.operations).sum+r.comparisons
def NativeArithmeticWordResult.evaluationActions {m : ℕ} (r : NativeArithmeticWordResult m) : ℕ :=
  (r.evaluations.map (fun run => run.trace.booleanActions)).sum
def NativeArithmeticWordResult.decisionActions {m : ℕ} (r : NativeArithmeticWordResult m) : ℕ :=
  (r.decisions.map WordDecisionTrace.actions).sum
def NativeArithmeticWordResult.booleanActions {m : ℕ} (r : NativeArithmeticWordResult m) : ℕ :=
  r.evaluationActions+r.decisionActions

theorem NativeScalarExpression.operations_one_le (e : NativeScalarExpression) : 1≤e.operations :=
  ScalarExpression.operations_one_le e.interpret

theorem nativeScalarExpressionList_length_le_operations (es : List NativeScalarExpression) :
    es.length≤(es.map NativeScalarExpression.operations).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h:=NativeScalarExpression.operations_one_le e
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem nativeScalarExpressionList_booleanActions (es : List NativeScalarExpression) (B : ℕ)
    (h : ∀ e∈es,e.integerBitBudget≤B) :
    (es.map (fun e => e.wordRun.trace.booleanActions)).sum≤
      wordNodeBooleanBudget B*(es.map NativeScalarExpression.operations).sum := by
  induction es with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons e es ih =>
    have he:=NativeScalarExpression.wordRun_booleanActions e B (h e (by simp))
    have ht:=ih (fun f hf => h f (by simp [hf]))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add he ht

theorem NativeArithmeticWordResult.evaluationActions_bound {m : ℕ} (r : NativeArithmeticWordResult m)
    (hmatch : r.evaluations=r.expressions.map NativeScalarExpression.wordRun)
    (B : ℕ) (hB : r.integerBitBudget≤B) :
    r.evaluationActions≤wordNodeBooleanBudget B*r.operations := by
  have h:=nativeScalarExpressionList_booleanActions r.expressions B (by
    intro e he
    exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)).trans hB)
  simp only [NativeArithmeticWordResult.evaluationActions,hmatch,List.map_map,Function.comp_apply]
  apply h.trans
  apply Nat.mul_le_mul_left
  exact Nat.le_add_right _ _

theorem nativeTracedPairWord_evaluationActions {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : NativePacketExpressionOracle) (B : ℕ)
    (hB : (nativeTracedPairWord entry inverseLabel table k f).integerBitBudget≤B) :
    (nativeTracedPairWord entry inverseLabel table k f).evaluationActions≤
      wordNodeBooleanBudget B*(nativeTracedPairWord entry inverseLabel table k f).operations :=
  NativeArithmeticWordResult.evaluationActions_bound _ (nativeTracedPairWord_evaluations _ _ _ _ _) B hB

theorem nativeTracedBase_decisionActions {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : NativePacketExpressionOracle) (B : ℕ)
    (hB : (nativeTracedBase entry table f).integerBitBudget≤B) :
    (nativeTracedBase entry table f).decisionActions≤wordDecisionBooleanBudget B*
      ((nativeTracedBase entry table f).expressions.length+(nativeTracedBase entry table f).comparisons) := by
  let scores:=List.Vector.ofFn (fun j => nativeExpressionDistance f (nativeExpressionWord entry (table j)) 20)
  let stored:=scores.map NativeScalarExpression.wordRun
  have hsum : (∑ i : Fin (n+1),(scores.get i).integerBitBudget)≤B := by
    simpa only [nativeTracedBase,NativeArithmeticWordResult.integerBitBudget,List.Vector.toList_ofFn,List.map_ofFn,
      List.sum_ofFn,Function.comp_apply,scores,List.Vector.get_ofFn] using hB
  have hi : ∀ i,(scores.get i).integerBitBudget≤B := by
    intro i
    exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores.get j).integerBitBudget))
      (Finset.mem_univ i)).trans hsum
  have hc:=wordMinimumProgram_height_actions n (stored.map ScalarWordEvaluation.value) B (by
    intro i
    simpa only [stored,List.Vector.get_map] using NativeScalarExpression.wordRun_height (scores.get i) B (hi i))
  change (wordMinimumProgram n (stored.map ScalarWordEvaluation.value)).trace.actions≤
    wordDecisionBooleanBudget B*(scores.toList.length+n)
  have hlen : scores.toList.length=n+1 := scores.2
  rw [hlen]
  dsimp only [wordDecisionBooleanBudget]
  nlinarith

theorem nativeTracedCorrection_decisionActions {m : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : NativePacketExpressionOracle → NativeArithmeticWordResult m)
    (ha : ∀ f B,(approx f).integerBitBudget≤B →
      (approx f).decisionActions≤wordDecisionBooleanBudget B*
        ((approx f).expressions.length+(approx f).comparisons))
    (t : ℕ) (f : NativePacketExpressionOracle) (B : ℕ)
    (hB : (nativeTracedCorrection entry inverseLabel approx t f).integerBitBudget≤B) :
    (nativeTracedCorrection entry inverseLabel approx t f).decisionActions≤wordDecisionBooleanBudget B*
      ((nativeTracedCorrection entry inverseLabel approx t f).expressions.length+
        (nativeTracedCorrection entry inverseLabel approx t f).comparisons) := by
  let u:=approx f
  let residual:=nativeExpressionPacketMul f (nativeExpressionPacketInverse (nativeExpressionWord entry u.word))
  let score:=nativeExpressionDistance residual nativeExpressionPacketOne (2*t+2)
  let threshold:=NativeScalarExpression.stoppingThreshold t
  let a:=approx (nativeExpressionFactorX residual t)
  let b:=approx (nativeExpressionFactorY residual t)
  let comparison:=wordScalarLEProgram score.wordRun.value threshold.wordRun.value
  unfold nativeTracedCorrection at hB ⊢
  dsimp only at hB ⊢
  split_ifs at hB ⊢
  · change ((u.expressions++[score,threshold]).map NativeScalarExpression.integerBitBudget).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.integerBitBudget≤B := by change (u.expressions.map NativeScalarExpression.integerBitBudget).sum≤B;omega
    have hs : score.integerBitBudget≤B := by omega
    have ht : threshold.integerBitBudget≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hc:=wordScalarLEProgram_height_actions score.wordRun.value threshold.wordRun.value B
      (NativeScalarExpression.wordRun_height score B hs) (NativeScalarExpression.wordRun_height threshold B ht)
    simp only [NativeArithmeticWordResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.expressions++[score,threshold]).length+(u.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi ⊢
    nlinarith
  · change ((u.expressions++[score,threshold]++a.expressions++b.expressions).map
        NativeScalarExpression.integerBitBudget).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.integerBitBudget≤B := by change (u.expressions.map NativeScalarExpression.integerBitBudget).sum≤B;omega
    have haB : a.integerBitBudget≤B := by change (a.expressions.map NativeScalarExpression.integerBitBudget).sum≤B;omega
    have hbB : b.integerBitBudget≤B := by change (b.expressions.map NativeScalarExpression.integerBitBudget).sum≤B;omega
    have hs : score.integerBitBudget≤B := by omega
    have ht : threshold.integerBitBudget≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hai : a.decisionActions≤wordDecisionBooleanBudget B*(a.expressions.length+a.comparisons) := ha _ B haB
    have hbi : b.decisionActions≤wordDecisionBooleanBudget B*(b.expressions.length+b.comparisons) := ha _ B hbB
    have hc:=wordScalarLEProgram_height_actions score.wordRun.value threshold.wordRun.value B
      (NativeScalarExpression.wordRun_height score B hs) (NativeScalarExpression.wordRun_height threshold B ht)
    simp only [NativeArithmeticWordResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)+a.decisionActions+b.decisionActions≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.expressions++[score,threshold]++a.expressions++b.expressions).length+
      (u.comparisons+a.comparisons+b.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi hai hbi ⊢
    nlinarith

theorem nativeTracedPairWord_decisionActions {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : NativePacketExpressionOracle) (B : ℕ)
    (hB : (nativeTracedPairWord entry inverseLabel table k f).integerBitBudget≤B) :
    (nativeTracedPairWord entry inverseLabel table k f).decisionActions≤wordDecisionBooleanBudget B*
      ((nativeTracedPairWord entry inverseLabel table k f).expressions.length+
        (nativeTracedPairWord entry inverseLabel table k f).comparisons) := by
  induction k generalizing f B with
  | zero => exact nativeTracedBase_decisionActions entry table f B hB
  | succ k ih =>
    exact nativeTracedCorrection_decisionActions entry inverseLabel _
      (fun g B hg => nativeTracedCorrection_decisionActions entry inverseLabel _ ih (numericalThreshold k) g B hg)
      (numericalThreshold k) f B hB

theorem nativeTracedPairWord_booleanActions {m n : ℕ} (entry : Fin m → NativePacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : NativePacketExpressionOracle) (B : ℕ)
    (hB : (nativeTracedPairWord entry inverseLabel table k f).integerBitBudget≤B) :
    (nativeTracedPairWord entry inverseLabel table k f).booleanActions≤
      2*wordNodeBooleanBudget B*(nativeTracedPairWord entry inverseLabel table k f).operations := by
  let r:=nativeTracedPairWord entry inverseLabel table k f
  have he:=nativeTracedPairWord_evaluationActions entry inverseLabel table k f B hB
  have hd:=nativeTracedPairWord_decisionActions entry inverseLabel table k f B hB
  have hlen:=nativeScalarExpressionList_length_le_operations r.expressions
  have hdec:=wordDecisionBooleanBudget_le B
  have hslots : r.expressions.length+r.comparisons≤r.operations :=
    Nat.add_le_add_right hlen _
  have hcost:=Nat.mul_le_mul hdec hslots
  change r.evaluationActions≤_ at he
  change r.decisionActions≤_ at hd
  change r.booleanActions≤_
  dsimp only [NativeArithmeticWordResult.booleanActions]
  nlinarith

end CircuitRecursion
