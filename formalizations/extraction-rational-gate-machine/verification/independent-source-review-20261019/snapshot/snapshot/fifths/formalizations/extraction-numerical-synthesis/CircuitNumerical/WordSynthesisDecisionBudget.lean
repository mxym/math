import CircuitNumerical.WordSynthesisEvaluationBudget

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem wordTracedBase_decisionActions {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (table : Fin (n+1) → List (Fin m)) (f : PacketExpressionOracle) (B : ℕ)
    (hB : (wordTracedBase entry table f).result.integerBitBudget≤B) :
    (wordTracedBase entry table f).decisionActions≤wordDecisionBooleanBudget B*
      ((wordTracedBase entry table f).result.expressions.length+(wordTracedBase entry table f).result.comparisons) := by
  let scores:=List.Vector.ofFn (fun j => expressionDistance f (expressionWord entry (table j)) 20)
  let stored:=scores.map ScalarExpression.wordRun
  have hsum : (∑ i : Fin (n+1),(scores.get i).integerBitBudget)≤B := by
    simpa only [wordTracedBase,ArithmeticWordResult.integerBitBudget,List.Vector.toList_ofFn,List.map_ofFn,
      List.sum_ofFn,Function.comp_apply,scores,List.Vector.get_ofFn] using hB
  have hi : ∀ i,(scores.get i).integerBitBudget≤B := by
    intro i
    exact (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Nat.zero_le ((scores.get j).integerBitBudget))
      (Finset.mem_univ i)).trans hsum
  have hc:=wordMinimumProgram_height_actions n (stored.map ScalarWordEvaluation.value) B (by
    intro i
    simpa only [stored,List.Vector.get_map] using ScalarExpression.wordRun_height (scores.get i) B (hi i))
  change (wordMinimumProgram n (stored.map ScalarWordEvaluation.value)).trace.actions≤
    wordDecisionBooleanBudget B*(scores.toList.length+n)
  have hlen : scores.toList.length=n+1 := scores.2
  rw [hlen]
  dsimp only [wordDecisionBooleanBudget]
  nlinarith

theorem wordTracedCorrection_decisionActions {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (approx : PacketExpressionOracle → WordArithmeticResult m)
    (ha : ∀ f B,(approx f).result.integerBitBudget≤B →
      (approx f).decisionActions≤wordDecisionBooleanBudget B*
        ((approx f).result.expressions.length+(approx f).result.comparisons))
    (t : ℕ) (f : PacketExpressionOracle) (B : ℕ)
    (hB : (wordTracedCorrection entry inverseLabel approx t f).result.integerBitBudget≤B) :
    (wordTracedCorrection entry inverseLabel approx t f).decisionActions≤wordDecisionBooleanBudget B*
      ((wordTracedCorrection entry inverseLabel approx t f).result.expressions.length+
        (wordTracedCorrection entry inverseLabel approx t f).result.comparisons) := by
  let u:=approx f
  let residual:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.result.word))
  let score:=expressionDistance residual expressionPacketOne (2*t+2)
  let threshold:=ScalarExpression.stoppingThreshold t
  let a:=approx (expressionFactorX residual t)
  let b:=approx (expressionFactorY residual t)
  let comparison:=wordScalarLEProgram score.wordRun.value threshold.wordRun.value
  unfold wordTracedCorrection at hB ⊢
  dsimp only at hB ⊢
  split_ifs at hB ⊢
  · change ((u.result.expressions++[score,threshold]).map ScalarExpression.integerBitBudget).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.result.integerBitBudget≤B := by change (u.result.expressions.map ScalarExpression.integerBitBudget).sum≤B;omega
    have hs : score.integerBitBudget≤B := by omega
    have ht : threshold.integerBitBudget≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hc:=wordScalarLEProgram_height_actions score.wordRun.value threshold.wordRun.value B
      (ScalarExpression.wordRun_height score B hs) (ScalarExpression.wordRun_height threshold B ht)
    simp only [WordArithmeticResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.result.expressions++[score,threshold]).length+(u.result.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi ⊢
    nlinarith
  · change ((u.result.expressions++[score,threshold]++a.result.expressions++b.result.expressions).map
        ScalarExpression.integerBitBudget).sum≤B at hB
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil] at hB
    have hu : u.result.integerBitBudget≤B := by change (u.result.expressions.map ScalarExpression.integerBitBudget).sum≤B;omega
    have haB : a.result.integerBitBudget≤B := by change (a.result.expressions.map ScalarExpression.integerBitBudget).sum≤B;omega
    have hbB : b.result.integerBitBudget≤B := by change (b.result.expressions.map ScalarExpression.integerBitBudget).sum≤B;omega
    have hs : score.integerBitBudget≤B := by omega
    have ht : threshold.integerBitBudget≤B := by omega
    have hi:=ha f B hu
    change u.decisionActions≤_ at hi
    have hai : a.decisionActions≤wordDecisionBooleanBudget B*(a.result.expressions.length+a.result.comparisons) := ha _ B haB
    have hbi : b.decisionActions≤wordDecisionBooleanBudget B*(b.result.expressions.length+b.result.comparisons) := ha _ B hbB
    have hc:=wordScalarLEProgram_height_actions score.wordRun.value threshold.wordRun.value B
      (ScalarExpression.wordRun_height score B hs) (ScalarExpression.wordRun_height threshold B ht)
    simp only [WordArithmeticResult.decisionActions,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,WordDecisionTrace.actions,Nat.add_zero]
    change u.decisionActions+(comparison.actions+4)+a.decisionActions+b.decisionActions≤_
    change comparison.actions≤_ at hc
    change _≤wordDecisionBooleanBudget B*((u.result.expressions++[score,threshold]++a.result.expressions++b.result.expressions).length+
      (u.result.comparisons+a.result.comparisons+b.result.comparisons+1))
    simp only [List.length_append,List.length_cons,List.length_nil]
    dsimp only [wordDecisionBooleanBudget] at hi hai hbi ⊢
    nlinarith

theorem wordTracedPairWord_decisionActions {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : PacketExpressionOracle) (B : ℕ)
    (hB : (wordTracedPairWord entry inverseLabel table k f).result.integerBitBudget≤B) :
    (wordTracedPairWord entry inverseLabel table k f).decisionActions≤wordDecisionBooleanBudget B*
      ((wordTracedPairWord entry inverseLabel table k f).result.expressions.length+
        (wordTracedPairWord entry inverseLabel table k f).result.comparisons) := by
  induction k generalizing f B with
  | zero => exact wordTracedBase_decisionActions entry table f B hB
  | succ k ih =>
    exact wordTracedCorrection_decisionActions entry inverseLabel _
      (fun g B hg => wordTracedCorrection_decisionActions entry inverseLabel _ ih (numericalThreshold k) g B hg)
      (numericalThreshold k) f B hB

theorem wordTracedPairWord_booleanActions {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : PacketExpressionOracle) (B : ℕ)
    (hB : (wordTracedPairWord entry inverseLabel table k f).result.integerBitBudget≤B) :
    (wordTracedPairWord entry inverseLabel table k f).booleanActions≤
      2*wordNodeBooleanBudget B*(wordTracedPairWord entry inverseLabel table k f).result.operations := by
  let r:=wordTracedPairWord entry inverseLabel table k f
  have he:=wordTracedPairWord_evaluationActions entry inverseLabel table k f B hB
  have hd:=wordTracedPairWord_decisionActions entry inverseLabel table k f B hB
  have hlen:=scalarExpressionList_length_le_operations r.result.expressions
  have hdec:=wordDecisionBooleanBudget_le B
  have hslots : r.result.expressions.length+r.result.comparisons≤r.result.operations :=
    Nat.add_le_add_right hlen _
  have hcost:=Nat.mul_le_mul hdec hslots
  change r.evaluationActions≤_ at he
  change r.decisionActions≤_ at hd
  change r.booleanActions≤_
  dsimp only [WordArithmeticResult.booleanActions]
  nlinarith

end CircuitRecursion
