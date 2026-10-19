import CircuitNumerical.IntegerSubtreeBounds

namespace CircuitRecursion

/-- A packet provider supplies a finite common-denominator representation at
each requested precision. This interface describes input operands, rather
than presupposing the synthesis program's correctness or running time. -/
def PacketOracleHeight (f : QuaternionOracle) (P B : ℕ) : Prop :=
  ∀ q,q≤P → ∃ a : IntegerPacket,a.value=f q ∧ IntegerPacketHeight a B

def cachedRationalPacketExpression (f : QuaternionOracle) (P : ℕ) : PacketExpressionOracle := fun q =>
  .literal (readPacketCache (buildPacketCache f P).1 q)

theorem cachedRationalPacketExpression_bitEnvelope (f : QuaternionOracle) (P B : ℕ)
    (hf : PacketOracleHeight f P B) :
    PacketBitEnvelope (cachedRationalPacketExpression f P) (0,4*(B+1)) := by
  intro q
  change (cachedRationalPacketExpression f P q).integerBitBudget≤0*q+4*(B+1)
  simp only [zero_mul,zero_add]
  by_cases hq : q≤P
  · obtain ⟨a,ha,hheight⟩:=hf q hq
    have hs : ∀ i,rationalBinaryExponent (a.value.get i)≤B+1 := by
      intro i
      rw [← IntegerPacket.coordinate_value]
      exact rationalBinaryExponent_le _ B (IntegerPacket.coordinate_height a B hheight i)
    have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => hs i)
    have hc:=buildPacketCache_agrees f P q hq
    simpa only [cachedRationalPacketExpression,PacketExpression.integerBitBudget,
      zero_mul,zero_add,hc,← ha,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hsum
  · have hone:=expressionPacketOne_bitEnvelope q
    have hc : readPacketCache (buildPacketCache f P).1 q=quaternionOracleOne q := by
      simp only [readPacketCache,dite_eq_right hq]
    change (cachedRationalPacketExpression f P q).integerBitBudget≤4*(B+1)
    have heq : cachedRationalPacketExpression f P q=expressionPacketOne q := by
      simp only [cachedRationalPacketExpression,hc]
      rfl
    rw [heq]
    exact hone.trans (by omega)

theorem cachedArithmeticRun_eq_rationalPacketExpression {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    cachedArithmeticRun entry inverseLabel table L p f=
    tracedPairWord (fun i => cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1))))
      inverseLabel table (Nat.clog 2 (p+1))
      (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) := by
  simp only [cachedArithmeticRun,List.Vector.get_ofFn]
  rfl

theorem cachedArithmeticRun_envelope_integerBitBudget {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketBitEnvelope
      (cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1)))) (0,B))
    (hf : PacketBitEnvelope
      (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) (0,B)) :
    (cachedArithmeticRun entry inverseLabel table L p f).integerBitBudget≤
      1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128 := by
  rw [cachedArithmeticRun_eq_rationalPacketExpression]
  have h:=tracedPairWord_flat_integerBitBudget
    (fun i => cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1))))
    B he inverseLabel table L (Nat.clog 2 (p+1)) hL
    (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) hf
  exact h.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (1000000000002*(n+1)*(B+2)*(L+1)) (traceRGrowth_precision_bound p))

/-- The cached arithmetic trace has a budget linear in the explicitly
represented input packet height and polynomial in the requested precision.
In particular, arbitrary rational angle providers need not be replaced by a
dyadic provider to use this estimate. -/
theorem cachedArithmeticRun_rational_integerBitBudget {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketOracleHeight (entry i) (numericalDemand L (Nat.clog 2 (p+1))) B)
    (hf : PacketOracleHeight f (numericalDemand L (Nat.clog 2 (p+1))) B) :
    (cachedArithmeticRun entry inverseLabel table L p f).integerBitBudget≤
      1000000000002*(n+1)*(4*(B+1)+2)*(L+1)*traceRGrowth*(p+1)^128 := by
  rw [cachedArithmeticRun_eq_rationalPacketExpression]
  have h:=tracedPairWord_flat_integerBitBudget
    (fun i => cachedRationalPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1))))
    (4*(B+1)) (fun i => cachedRationalPacketExpression_bitEnvelope _ _ _ (he i))
    inverseLabel table L (Nat.clog 2 (p+1)) hL
    (cachedRationalPacketExpression f (numericalDemand L (Nat.clog 2 (p+1))))
    (cachedRationalPacketExpression_bitEnvelope _ _ _ hf)
  exact h.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (1000000000002*(n+1)*(4*(B+1)+2)*(L+1)) (traceRGrowth_precision_bound p))

theorem cachedArithmeticRun_rational_expression_integerSubtreeBound {m n : ℕ}
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : QuaternionOracle)
    (he : ∀ i,PacketOracleHeight (entry i) (numericalDemand L (Nat.clog 2 (p+1))) B)
    (hf : PacketOracleHeight f (numericalDemand L (Nat.clog 2 (p+1))) B)
    (e : ScalarExpression) (hmem : e∈(cachedArithmeticRun entry inverseLabel table L p f).expressions) :
    e.IntegerSubtreeBound
      (1000000000002*(n+1)*(4*(B+1)+2)*(L+1)*traceRGrowth*(p+1)^128) := by
  apply ScalarExpression.integerSubtreeBound
  exact (List.le_sum_of_mem (List.mem_map.mpr ⟨e,hmem,rfl⟩)).trans
    (cachedArithmeticRun_rational_integerBitBudget entry inverseLabel table L p B hL f he hf)

end CircuitRecursion
