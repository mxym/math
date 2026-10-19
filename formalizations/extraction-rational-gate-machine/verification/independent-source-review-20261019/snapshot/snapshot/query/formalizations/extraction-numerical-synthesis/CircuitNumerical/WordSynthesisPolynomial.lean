import CircuitNumerical.WordSynthesisDecisionBudget
import CircuitNumerical.RawOperationGrowth

namespace CircuitRecursion

set_option maxHeartbeats 1500000

/-- General algebraic composition of already explicit AST height/operation
budgets. Neither hypothesis is a runtime or final-correctness certificate. -/
theorem wordTracedPairWord_booleanActions_power_bound {m n : ℕ}
    (entry : Fin m → PacketExpressionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : PacketExpressionOracle)
    (p a b C O : ℕ)
    (hbit : (wordTracedPairWord entry inverseLabel table k f).result.integerBitBudget≤C*(p+1)^a)
    (hops : (wordTracedPairWord entry inverseLabel table k f).result.operations≤O*(p+1)^b) :
    (wordTracedPairWord entry inverseLabel table k f).booleanActions≤
      40000*(2*C+4)^2*O*(p+1)^(2*a+b) := by
  have hc:=wordTracedPairWord_booleanActions entry inverseLabel table k f (C*(p+1)^a) hbit
  have hpos : 1≤(p+1)^a := Nat.one_le_pow _ _ (by omega)
  have hbase : 2*(C*(p+1)^a)+4≤(2*C+4)*(p+1)^a := by nlinarith
  have hp:=Nat.pow_le_pow_left hbase 2
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 40000 hp) hops
  apply hc.trans
  calc
    _≤(40000*((2*C+4)*(p+1)^a)^2)*(O*(p+1)^b) := by
      convert hm using 1 <;> dsimp only [wordNodeBooleanBudget] <;> ring
    _=40000*(2*C+4)^2*O*(p+1)^(2*a+b) := by
      simp only [mul_pow,←pow_mul]
      rw [pow_add]
      have he : 2*a=a*2 := by omega
      rw [he]
      ring

/-- A closed action bound for the actual Word synthesis recursion under the
explicit input expression envelopes. Provider execution and literal adapter
runtime are not inferred from those envelopes. -/
theorem wordTracedPairWord_twenty_booleanActions {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 20) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : PacketExpressionOracle) (hf : PacketOperationBound f 20)
    (heB : ∀ i,PacketBitEnvelope (entry i) (0,B)) (hfB : PacketBitEnvelope f (0,B)) :
    let C:=1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (wordTracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).booleanActions≤
      40000*(2*C+4)^2*O*(p+1)^320 := by
  dsimp only
  let C:=1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth
  let O:=1020*(n+1)*(2*L+1)*offsetGrowth
  have hb : (wordTracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).result.integerBitBudget≤C*(p+1)^128 := by
    rw [wordTracedPairWord_result]
    have h:=tracedPairWord_flat_integerBitBudget entry B heB inverseLabel table L
      (Nat.clog 2 (p+1)) hL f hfB
    exact h.trans (by simpa only [C,Nat.mul_assoc] using
      Nat.mul_le_mul_left (1000000000002*(n+1)*(B+2)*(L+1)) (traceRGrowth_precision_bound p))
  have ho : (wordTracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).result.operations≤O*(p+1)^64 := by
    rw [wordTracedPairWord_result]
    exact tracedPairWord_twenty_precision_operations entry he inverseLabel table L p hL f hf
  exact wordTracedPairWord_booleanActions_power_bound entry inverseLabel table _ f p 128 64 C O hb ho

theorem wordRawPacketPairWord_booleanActions {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p A : ℕ) (hL : ∀ j,(table j).length≤L) (f : ℕ → IntegerPacket)
    (he : ∀ i r,IntegerPacketHeight (entry i r) A) (hf : ∀ r,IntegerPacketHeight (f r) A) :
    let C:=1000000000002*(n+1)*(8*(A+1)+2)*(L+1)*traceRGrowth
    let O:=1020*(n+1)*(2*L+1)*offsetGrowth
    (wordTracedPairWord (fun i => rawPacketExpressionOracle (entry i)) inverseLabel table
      (Nat.clog 2 (p+1)) (rawPacketExpressionOracle f)).booleanActions≤40000*(2*C+4)^2*O*(p+1)^320 := by
  exact wordTracedPairWord_twenty_booleanActions _ (fun i => rawPacketExpressionOracle_operationBound (entry i))
    inverseLabel table L p (8*(A+1)) hL _ (rawPacketExpressionOracle_operationBound f)
    (fun i => rawPacketExpressionOracle_bitEnvelope (entry i) A (he i))
    (rawPacketExpressionOracle_bitEnvelope f A hf)

end CircuitRecursion
