import CircuitRecursion.ExpressionResources

namespace CircuitRecursion

set_option maxRecDepth 4096

theorem expressionWord_bound {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 1) (w : List (Fin m)) :
    PacketOperationBound (expressionWord entry w) (49*w.length+1) := by
  induction w with
  | nil => exact fun _ => le_refl 1
  | cons i w ih =>
    have h := expressionPacketMul_bound _ _ _ _ ih (he i)
    convert h using 1 <;> first | rfl | simp only [List.length_cons]; ring

theorem tracedBase_operations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 1) (table : Fin (n+1) → List (Fin m))
    (L : ℕ) (hL : ∀ j,(table j).length≤L) (f : PacketExpressionOracle)
    (C : ℕ) (hf : PacketOperationBound f C) :
    (tracedBase entry table f).operations≤(n+1)*C+((n+1)*(49*L+17)+n) := by
  have hs : ∀ j,(expressionDistance f (expressionWord entry (table j)) 20).operations≤C+49*L+17 := by
    intro j
    have h := expressionDistance_bound _ _ _ _ hf (expressionWord_bound entry he (table j)) 20
    have hl := hL j
    omega
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hs j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  simp only [ArithmeticWordResult.operations,tracedBase,List.Vector.toList_ofFn,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  nlinarith

def correctionOperationSlope (A : ℕ) : ℕ := 100001*A+1
def correctionOperationOffset (A B L : ℕ) : ℕ :=
  3*B+100000*A*(49*L+54)+2*A+49*L+75

def WordOperationBound {m : ℕ} (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (A B : ℕ) : Prop :=
  ∀ (f : PacketExpressionOracle) (C : ℕ),PacketOperationBound f C → (approx f).operations≤A*C+B

theorem tracedCorrection_operations {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 1) (inverseLabel : Fin m → Fin m)
    (approx : PacketExpressionOracle → ArithmeticWordResult m) (A B L t : ℕ)
    (hL : ∀ f,(approx f).word.length≤L) (ha : WordOperationBound approx A B) :
    WordOperationBound (tracedCorrection entry inverseLabel approx t)
      (correctionOperationSlope A) (correctionOperationOffset A B L) := by
  intro f C hf
  let u := approx f
  let r := expressionPacketMul f (expressionPacketInverse (expressionWord entry u.word))
  let score := expressionDistance r expressionPacketOne (2*t+2)
  have hu := ha f C hf
  have hw := expressionWord_bound entry he u.word
  have hl : u.word.length≤L := hL f
  have hr : PacketOperationBound r (C+49*L+53) := by
    intro p
    have h := expressionPacketMul_bound _ _ _ _ hf (expressionPacketInverse_bound _ _ hw) p
    dsimp only [r]
    omega
  have hs : score.operations≤C+49*L+70 := by
    have h := expressionDistance_bound r expressionPacketOne _ 1 hr (fun _ => le_refl 1) (2*t+2)
    exact h
  have hx := (expressionFactor_bounds r _ t hr).1
  have hy := (expressionFactor_bounds r _ t hr).2
  have hax := ha (expressionFactorX r t) _ hx
  have hay := ha (expressionFactorY r t) _ hy
  change (if score.eval≤2*((1/2:ℚ)^t)^2 then
    ⟨u.word,u.expressions++[score,.stoppingThreshold t],u.comparisons+1⟩ else
    ⟨u.word++instructionInverse inverseLabel (approx (expressionFactorY r t)).word++
      instructionInverse inverseLabel (approx (expressionFactorX r t)).word++
      (approx (expressionFactorY r t)).word++(approx (expressionFactorX r t)).word,
      u.expressions++[score,.stoppingThreshold t]++(approx (expressionFactorX r t)).expressions++(approx (expressionFactorY r t)).expressions,
      u.comparisons+(approx (expressionFactorX r t)).comparisons+(approx (expressionFactorY r t)).comparisons+1⟩
      : ArithmeticWordResult m).operations≤_
  split_ifs
  · simp only [ArithmeticWordResult.operations,List.map_append,List.sum_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,ScalarExpression.operations]
    change u.operations≤_ at hu
    unfold ArithmeticWordResult.operations at hu
    unfold correctionOperationSlope correctionOperationOffset
    nlinarith
  · simp only [ArithmeticWordResult.operations,List.map_append,List.sum_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,ScalarExpression.operations]
    change u.operations≤_ at hu
    unfold ArithmeticWordResult.operations at hu hax hay
    unfold correctionOperationSlope correctionOperationOffset
    nlinarith

def pairOperationSlope (n : ℕ) : ℕ → ℕ
  | 0 => n+1
  | k+1 => correctionOperationSlope (correctionOperationSlope (pairOperationSlope n k))
def pairOperationOffset (n L : ℕ) : ℕ → ℕ
  | 0 => (n+1)*(49*L+17)+n
  | k+1 => correctionOperationOffset (correctionOperationSlope (pairOperationSlope n k))
      (correctionOperationOffset (pairOperationSlope n k) (pairOperationOffset n L k) (L*25^k))
      (5*(L*25^k))

theorem tracedPairWord_operations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 1) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L) (k : ℕ) :
    WordOperationBound (tracedPairWord entry inverseLabel table k)
      (pairOperationSlope n k) (pairOperationOffset n L k) := by
  induction k with
  | zero => exact tracedBase_operations entry he table L hL
  | succ k ih =>
    have hlen : ∀ f,(tracedPairWord entry inverseLabel table k f).word.length≤L*25^k := by
      intro f
      rw [tracedPairWord_word]
      exact numericalPairWord_length _ _ table L hL k _
    have hinner := tracedCorrection_operations entry he inverseLabel _ _ _ _ (numericalThreshold k) hlen ih
    have hlen' : ∀ f,(tracedCorrection entry inverseLabel
        (tracedPairWord entry inverseLabel table k) (numericalThreshold k) f).word.length≤5*(L*25^k) := by
      intro f
      rw [tracedCorrection_word entry inverseLabel _ _ (tracedPairWord_word entry inverseLabel table k)]
      exact numericalCorrection_length _ _ _ (L*25^k) (numericalThreshold k)
        (numericalPairWord_length _ _ table L hL k) _
    exact tracedCorrection_operations entry he inverseLabel _ _ _ _ (numericalThreshold k) hlen' hinner

end CircuitRecursion
