import CircuitNumerical.NativeTraceRefinement

namespace CircuitRecursion

set_option maxHeartbeats 1500000

theorem nativeTracedPairWord_booleanActions_power_bound {m n : ℕ}
    (entry : Fin m → NativePacketExpressionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : NativePacketExpressionOracle)
    (p a b C O : ℕ)
    (hbit : (nativeTracedPairWord entry inverseLabel table k f).integerBitBudget≤C*(p+1)^a)
    (hops : (nativeTracedPairWord entry inverseLabel table k f).operations≤O*(p+1)^b) :
    (nativeTracedPairWord entry inverseLabel table k f).booleanActions≤
      40000*(2*C+4)^2*O*(p+1)^(2*a+b) := by
  have hc:=nativeTracedPairWord_booleanActions entry inverseLabel table k f (C*(p+1)^a) hbit
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

end CircuitRecursion
