import CircuitNumerical.FactorInputBounds

namespace CircuitRecursion

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

theorem bitFactorEnvelope_closed (a b t : ℕ) :
    bitFactorEnvelope (a,b) t=(12980*a+20576,
      (36288*a+57536)*t+455866*a+1459*b+728820) := by
  simp only [bitFactorEnvelope,bitConjugatorEnvelope,bitNormalizedEnvelope,bitRadiusEnvelope,
    bitChartMassEnvelope,bitChartTargetEnvelope,bitBalancedReferenceEnvelope,bitReferenceEnvelope,
    bitBalancedCEnvelope,bitBalancedSEnvelope,bitPacketMulEnvelope,bitDistanceEnvelope,
    bitMulEnvelope,bitInvEnvelope,bitAddEnvelope,bitSqrtEnvelope,bitMeanEnvelope]
  apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> ring

def ArithmeticWordResult.integerBitBudget {m : ℕ} (r : ArithmeticWordResult m) : ℕ :=
  (r.expressions.map ScalarExpression.integerBitBudget).sum

def TraceBitBound {m : ℕ} (approx : PacketExpressionOracle → ArithmeticWordResult m)
    (S T R : ℕ) : Prop :=
  ∀ (f : PacketExpressionOracle) (a b : ℕ),PacketBitEnvelope f (a,b) →
    (approx f).integerBitBudget≤S*a+T*b+R

theorem tracedBase_integerBitBudget {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (gateB : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,gateB))
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L) :
    TraceBitBound (tracedBase entry table) (52*(n+1)) (2*(n+1))
      ((n+1)*(2*(gateB+2)*L+12)) := by
  intro f a b hf
  have hs : ∀ j,(expressionDistance f (expressionWord entry (table j)) 20).integerBitBudget≤
      52*a+2*b+2*(gateB+2)*L+12 := by
    intro j
    have h:=bitDistance_bound f (expressionWord entry (table j)) (a,b) _ hf
      (expressionWord_bitEnvelope entry gateB he (table j)) 20
    have hl:=Nat.mul_le_mul_left (gateB+2) (hL j)
    simp only [bitDistanceEnvelope,Prod.fst,Prod.snd,zero_mul,zero_add,mul_zero] at h
    nlinarith
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => hs j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  simp only [ArithmeticWordResult.integerBitBudget,tracedBase,List.Vector.toList_ofFn,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  nlinarith

def correctionTraceS (S T t : ℕ) : ℕ := 25961*S+(72576*t+923404)*T+4*t+24
def correctionTraceT (T : ℕ) : ℕ := 2919*T+2
def correctionTraceR (S T R gateB L t : ℕ) : ℕ :=
  let W:=(gateB+2)*L+6
  3*R+41152*S+(115072*t+2918*W+1457640)*T+2*W+2*t+13

theorem tracedCorrection_integerBitBudget {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (gateB : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,gateB)) (inverseLabel : Fin m → Fin m)
    (approx : PacketExpressionOracle → ArithmeticWordResult m) (S T R L t : ℕ)
    (hL : ∀ f,(approx f).word.length≤L) (ha : TraceBitBound approx S T R) :
    TraceBitBound (tracedCorrection entry inverseLabel approx t)
      (correctionTraceS S T t) (correctionTraceT T) (correctionTraceR S T R gateB L t) := by
  intro f a b hf
  let u:=approx f
  let r:=expressionPacketMul f (expressionPacketInverse (expressionWord entry u.word))
  let score:=expressionDistance r expressionPacketOne (2*t+2)
  let W:=(gateB+2)*L+6
  have hu : u.integerBitBudget≤S*a+T*b+R := ha f a b hf
  have hr : PacketBitEnvelope r (a,4*a+b+W) := by
    intro q
    have h:=residual_bitEnvelope entry gateB he f (a,b) hf u.word q
    have hl:=Nat.mul_le_mul_left (gateB+2) (hL f)
    change (r q).integerBitBudget≤_ at h ⊢
    dsimp only [W]
    nlinarith
  have hx:=(bitFactor_bounds r (a,4*a+b+W) hr t).1
  have hy:=(bitFactor_bounds r (a,4*a+b+W) hr t).2
  rw [bitFactorEnvelope_closed] at hx hy
  have hax:=ha (expressionFactorX r t) _ _ hx
  have hay:=ha (expressionFactorY r t) _ _ hy
  have hs:=bitDistance_bound r expressionPacketOne (a,4*a+b+W) (0,4) hr
    expressionPacketOne_bitEnvelope (2*t+2)
  change score.integerBitBudget≤_ at hs
  simp only [bitDistanceEnvelope,Prod.fst,Prod.snd,zero_mul,zero_add,mul_zero] at hs
  have hall : u.integerBitBudget+(approx (expressionFactorX r t)).integerBitBudget+
      (approx (expressionFactorY r t)).integerBitBudget+score.integerBitBudget+(2*t+1)≤
      correctionTraceS S T t*a+correctionTraceT T*b+correctionTraceR S T R gateB L t := by
    unfold correctionTraceS correctionTraceT correctionTraceR
    dsimp only [W] at hax hay hs
    nlinarith
  change (if score.eval≤2*((1/2:ℚ)^t)^2 then
    ⟨u.word,u.expressions++[score,.stoppingThreshold t],u.comparisons+1⟩ else
    ⟨u.word++instructionInverse inverseLabel (approx (expressionFactorY r t)).word++
      instructionInverse inverseLabel (approx (expressionFactorX r t)).word++
      (approx (expressionFactorY r t)).word++(approx (expressionFactorX r t)).word,
      u.expressions++[score,.stoppingThreshold t]++(approx (expressionFactorX r t)).expressions++
        (approx (expressionFactorY r t)).expressions,
      u.comparisons+(approx (expressionFactorX r t)).comparisons+(approx (expressionFactorY r t)).comparisons+1⟩
      : ArithmeticWordResult m).integerBitBudget≤_
  split_ifs <;>
    simp only [ArithmeticWordResult.integerBitBudget,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ScalarExpression.integerBitBudget] <;>
    unfold ArithmeticWordResult.integerBitBudget at hall <;> omega

def pairTraceT (n : ℕ) : ℕ → ℕ
  | 0 => 2*(n+1)
  | k+1 => correctionTraceT (correctionTraceT (pairTraceT n k))
def pairTraceS (n : ℕ) : ℕ → ℕ
  | 0 => 52*(n+1)
  | k+1 => correctionTraceS
      (correctionTraceS (pairTraceS n k) (pairTraceT n k) (numericalThreshold k))
      (correctionTraceT (pairTraceT n k)) (numericalThreshold k)
def pairTraceR (n gateB L : ℕ) : ℕ → ℕ
  | 0 => (n+1)*(2*(gateB+2)*L+12)
  | k+1 => correctionTraceR
      (correctionTraceS (pairTraceS n k) (pairTraceT n k) (numericalThreshold k))
      (correctionTraceT (pairTraceT n k))
      (correctionTraceR (pairTraceS n k) (pairTraceT n k) (pairTraceR n gateB L k) gateB (L*25^k) (numericalThreshold k))
      gateB (5*(L*25^k)) (numericalThreshold k)

theorem tracedPairWord_integerBitBudget {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (gateB : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,gateB)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L) (k : ℕ) :
    TraceBitBound (tracedPairWord entry inverseLabel table k)
      (pairTraceS n k) (pairTraceT n k) (pairTraceR n gateB L k) := by
  induction k with
  | zero => exact tracedBase_integerBitBudget entry gateB he table L hL
  | succ k ih =>
    have hlen : ∀ f,(tracedPairWord entry inverseLabel table k f).word.length≤L*25^k := by
      intro f
      rw [tracedPairWord_word]
      exact numericalPairWord_length _ _ table L hL k _
    have hinner:=tracedCorrection_integerBitBudget entry gateB he inverseLabel _ _ _ _ _ (numericalThreshold k) hlen ih
    have hlen' : ∀ f,(tracedCorrection entry inverseLabel
        (tracedPairWord entry inverseLabel table k) (numericalThreshold k) f).word.length≤5*(L*25^k) := by
      intro f
      rw [tracedCorrection_word entry inverseLabel _ _ (tracedPairWord_word entry inverseLabel table k)]
      exact numericalCorrection_length _ _ _ (L*25^k) (numericalThreshold k)
        (numericalPairWord_length _ _ table L hL k) _
    exact tracedCorrection_integerBitBudget entry gateB he inverseLabel _ _ _ _ _ (numericalThreshold k) hlen' hinner

end CircuitRecursion
