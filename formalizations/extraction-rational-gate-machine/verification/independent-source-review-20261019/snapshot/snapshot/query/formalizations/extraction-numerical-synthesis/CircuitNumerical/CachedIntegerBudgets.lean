import CircuitNumerical.BitTraceGrowth

namespace CircuitRecursion

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

theorem tracedPairWord_flat_integerBitBudget {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (gateB : ℕ) (he : ∀ i,PacketBitEnvelope (entry i) (0,gateB))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : PacketExpressionOracle) (hf : PacketBitEnvelope f (0,gateB)) :
    (tracedPairWord entry inverseLabel table k f).integerBitBudget≤
      1000000000002*(n+1)*(gateB+2)*(L+1)*traceRGrowth^k := by
  have h:=tracedPairWord_integerBitBudget entry gateB he inverseLabel table L hL k f 0 gateB hf
  have ht:=Nat.mul_le_mul_right gateB (pairTraceT_bound n k)
  have hp : traceTGrowth^k≤traceRGrowth^k := Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceRGrowth]) _
  have hg : gateB≤(gateB+2)*(L+1) := by nlinarith
  have hT : pairTraceT n k*gateB≤2*(n+1)*(gateB+2)*(L+1)*traceRGrowth^k := by
    calc
      _≤(2*(n+1)*traceTGrowth^k)*gateB := ht
      _=(2*(n+1)*gateB)*traceTGrowth^k := by ring
      _≤(2*(n+1)*((gateB+2)*(L+1)))*traceRGrowth^k :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hg) hp
      _=_ := by ring
  have hR:=pairTraceR_bound n gateB L k
  simp only [mul_zero,zero_add] at h
  apply h.trans
  have hsum:=Nat.add_le_add hT hR
  convert hsum using 1 <;> first | rfl | ring


def cachedIntegerBudgetConstant (n L : ℕ) : ℕ :=
  10000000000020*(n+1)*(L+1)*(51200000*(L+1)+1)*traceRGrowth

theorem cachedIntegerBudget_algebra (n L p G : ℕ) :
    1000000000002*(n+1)*(10*(51200000*(L+1)+1)*(p+1)^9)*(L+1)*(G*(p+1)^128)=
      10000000000020*(n+1)*(L+1)*(51200000*(L+1)+1)*G*(p+1)^137 := by
  rw [show 137=9+128 by decide,pow_add]
  generalize p+1=x
  ring


theorem cachedArithmeticRun_eq_packetExpression {m n : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : DyadicQuaternionOracle) :
    cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)=
    tracedPairWord (fun i => cachedPacketExpression (entry i) (numericalDemand L (Nat.clog 2 (p+1))))
      inverseLabel table (Nat.clog 2 (p+1))
      (cachedPacketExpression f (numericalDemand L (Nat.clog 2 (p+1)))) := by
  simp only [cachedArithmeticRun,List.Vector.get_ofFn]
  rfl


/-- A polynomial bound on the actual cached finite arithmetic trace's
represented integer numerator/denominator exponent budget. This is separate
from the machine bit costs of the finite integer primitives. -/
theorem cachedArithmeticRun_integerBitBudget {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) :
    (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).integerBitBudget≤cachedIntegerBudgetConstant n L*(p+1)^137 := by
  let P:=numericalDemand L (Nat.clog 2 (p+1))
  let B:=4*(P+2)
  have h:=tracedPairWord_flat_integerBitBudget (fun i => cachedPacketExpression (entry i) P) B
    (fun i => cachedPacketExpression_bitEnvelope (entry i) (G i) (he i) P)
    inverseLabel table L (Nat.clog 2 (p+1)) hL (cachedPacketExpression f P)
    (cachedPacketExpression_bitEnvelope f U hf P)
  have hrun : (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).integerBitBudget≤
      1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth^Nat.clog 2 (p+1) := by
    rw [cachedArithmeticRun_eq_packetExpression]
    exact h
  have hP : P+1≤(51200000*(L+1)+1)*(p+1)^9 := by
    have h:=numericalDemand_precision_bound L p
    have h1 : 1≤(p+1)^9 := Nat.one_le_pow _ _ (by omega)
    dsimp [P]
    nlinarith
  have hB : B+2≤10*(51200000*(L+1)+1)*(p+1)^9 := by
    have hb : B+2≤10*(P+1) := by dsimp [B];omega
    have h:=Nat.mul_le_mul_left 10 hP
    exact hb.trans (by simpa only [Nat.mul_assoc] using h)
  have ht:=Nat.mul_le_mul
    (Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul_left (1000000000002*(n+1)) hB))
    (traceRGrowth_precision_bound p)
  apply hrun.trans
  exact ht.trans_eq (by simpa only [cachedIntegerBudgetConstant] using cachedIntegerBudget_algebra n L p traceRGrowth)


theorem ArithmeticWordResult.expression_integerHeight {m : ℕ} (r : ArithmeticWordResult m)
    (e : ScalarExpression) (he : e∈r.expressions) : IntegerScalarHeight e.integerRun r.integerBitBudget := by
  apply IntegerScalarHeight.mono _ _ _ (ScalarExpression.integerRun_height e)
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem cachedArithmeticRun_expression_integerHeight {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U)
    (e : ScalarExpression) (hmem : e∈(cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i))
      inverseLabel table L p (dyadicQuaternionOracle f)).expressions) :
    IntegerScalarHeight e.integerRun (cachedIntegerBudgetConstant n L*(p+1)^137) :=
  IntegerScalarHeight.mono _ _ _ (ArithmeticWordResult.expression_integerHeight _ e hmem)
    (cachedArithmeticRun_integerBitBudget entry G he inverseLabel table L p hL f U hf)

end CircuitRecursion
