import CircuitNumerical.FactorBitBudgets

namespace CircuitRecursion

def cachedPacketExpression (f : DyadicQuaternionOracle) (P : ℕ) : PacketExpressionOracle := fun q =>
  .literal (readPacketCache (buildPacketCache (dyadicQuaternionOracle f) P).1 q)

theorem cachedPacketExpression_bitEnvelope (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (P : ℕ) :
    PacketBitEnvelope (cachedPacketExpression f P) (0,4*(P+2)) := by
  intro q
  let a:=cachedIntegerPacket f P q
  have ha : IntegerPacketHeight a (P+1) := cachedIntegerPacket_height f U hf P q
  have he : a.value=readPacketCache (buildPacketCache (dyadicQuaternionOracle f) P).1 q :=
    cachedIntegerPacket_value f P q
  have hs : ∀ i,rationalBinaryExponent (a.value.get i)≤P+2 := by
    intro i
    rw [← IntegerPacket.coordinate_value]
    exact rationalBinaryExponent_le _ (P+1) (IntegerPacket.coordinate_height a (P+1) ha i)
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hs i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  simpa only [cachedPacketExpression,PacketExpression.integerBitBudget,zero_mul,zero_add,he] using h

theorem expressionPacketOne_bitEnvelope : PacketBitEnvelope expressionPacketOne (0,4) := by
  intro p
  norm_num [expressionPacketOne,PacketExpression.integerBitBudget,Fin.sum_univ_four]

theorem expressionWord_bitEnvelope {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (B : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,B)) (w : List (Fin m)) :
    PacketBitEnvelope (expressionWord entry w) (0,(B+2)*w.length+4) := by
  induction w with
  | nil => exact expressionPacketOne_bitEnvelope
  | cons i w ih =>
    have h:=bitPacketMul_bound _ _ _ _ ih (he i)
    convert h using 1 <;> first | rfl | simp only [bitPacketMulEnvelope,List.length_cons];ring

theorem residual_bitEnvelope {m : ℕ} (entry : Fin m → PacketExpressionOracle)
    (B : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,B))
    (f : PacketExpressionOracle) (e : BitEnvelope) (hf : PacketBitEnvelope f e) (w : List (Fin m)) :
    PacketBitEnvelope (expressionPacketMul f (expressionPacketInverse (expressionWord entry w)))
      (e.1,4*e.1+e.2+(B+2)*w.length+6) := by
  have h:=bitPacketMul_bound _ _ _ _ hf (bitPacketInverse_bound _ _ (expressionWord_bitEnvelope entry B he w))
  convert h using 1 <;> first | rfl | simp only [bitPacketMulEnvelope];ring

/-- The fixed-depth factor operand bound is obtained from actual cached
provider packets and the actual finite residual word. It is not an external
factor or polynomial-cost certificate. Nested recursion budgets remain separate. -/
theorem cachedResidualFactor_integerHeight {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U)
    (P t p : ℕ) (w : List (Fin m)) :
    let r:=expressionPacketMul (cachedPacketExpression f P)
      (expressionPacketInverse (expressionWord (fun i => cachedPacketExpression (entry i) P) w))
    IntegerPacketHeight (expressionFactorX r t p).integerRun
      (1000000*(4*(P+2)+(4*(P+2)+2)*w.length+6+p+t+1)) ∧
    IntegerPacketHeight (expressionFactorY r t p).integerRun
      (1000000*(4*(P+2)+(4*(P+2)+2)*w.length+6+p+t+1)) := by
  dsimp only
  let r:=expressionPacketMul (cachedPacketExpression f P)
    (expressionPacketInverse (expressionWord (fun i => cachedPacketExpression (entry i) P) w))
  have hr:=residual_bitEnvelope (fun i => cachedPacketExpression (entry i) P) (4*(P+2))
    (fun i => cachedPacketExpression_bitEnvelope (entry i) (G i) (he i) P)
    (cachedPacketExpression f P) (0,4*(P+2)) (cachedPacketExpression_bitEnvelope f U hf P) w
  have hr' : PacketBitEnvelope r (0,4*(P+2)+(4*(P+2)+2)*w.length+6) := by
    simpa only [r,zero_mul,mul_zero,zero_add] using hr
  have h:=fixedFactor_integerBitBudget r _ t p hr'
  exact ⟨IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height _) h.1,
    IntegerPacketHeight.mono _ _ _ (PacketExpression.integerRun_height _) h.2⟩

end CircuitRecursion
