import CircuitNumerical.WordNumericalExecution

namespace CircuitRecursion

theorem ScalarExpression.operations_one_le (e : ScalarExpression) : 1≤e.operations := by
  cases e <;> simp only [ScalarExpression.operations] <;> omega

theorem scalarExpressionList_length_le_operations (es : List ScalarExpression) :
    es.length≤(es.map ScalarExpression.operations).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h:=ScalarExpression.operations_one_le e
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem scalarExpressionList_booleanActions (es : List ScalarExpression) (B : ℕ)
    (h : ∀ e∈es,e.integerBitBudget≤B) :
    (es.map (fun e => e.wordRun.trace.booleanActions)).sum≤
      wordNodeBooleanBudget B*(es.map ScalarExpression.operations).sum := by
  induction es with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons e es ih =>
    have he:=ScalarExpression.wordRun_booleanActions e B (h e (by simp))
    have ht:=ih (fun f hf => h f (by simp [hf]))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add he ht

theorem WordArithmeticResult.evaluationActions_bound {m : ℕ} (r : WordArithmeticResult m)
    (hmatch : r.evaluations=r.result.expressions.map ScalarExpression.wordRun)
    (B : ℕ) (hB : r.result.integerBitBudget≤B) :
    r.evaluationActions≤wordNodeBooleanBudget B*r.result.operations := by
  have h:=scalarExpressionList_booleanActions r.result.expressions B (by
    intro e he
    exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)).trans hB)
  simp only [WordArithmeticResult.evaluationActions,hmatch,List.map_map,Function.comp_apply]
  apply h.trans
  apply Nat.mul_le_mul_left
  exact Nat.le_add_right _ _

theorem wordTracedPairWord_evaluationActions {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (k : ℕ) (f : PacketExpressionOracle) (B : ℕ)
    (hB : (wordTracedPairWord entry inverseLabel table k f).result.integerBitBudget≤B) :
    (wordTracedPairWord entry inverseLabel table k f).evaluationActions≤
      wordNodeBooleanBudget B*(wordTracedPairWord entry inverseLabel table k f).result.operations :=
  WordArithmeticResult.evaluationActions_bound _ (wordTracedPairWord_evaluations _ _ _ _ _) B hB

def wordDecisionBooleanBudget (B : ℕ) : ℕ := 400*(B+2)^2+5

theorem wordDecisionBooleanBudget_le (B : ℕ) : wordDecisionBooleanBudget B≤wordNodeBooleanBudget B := by
  have h:=wordNodeBooleanBudget_square B 400 (B+2) (by omega) (by omega)
  dsimp only [wordDecisionBooleanBudget]
  omega

end CircuitRecursion
