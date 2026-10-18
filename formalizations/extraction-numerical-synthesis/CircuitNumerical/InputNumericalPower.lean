import CircuitNumerical.InputNumericalBudgets

namespace CircuitRecursion

set_option maxHeartbeats 1500000

theorem inputTracedPairWord_numericalActions_power_bound {m n P : ℕ} (cache : NativeCacheEnvironment m P)
    (entry : Fin m → InputPacketExpressionOracle m) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (k : ℕ) (f : InputPacketExpressionOracle m)
    (p a b C O : ℕ)
    (hbit : (inputTracedPairWord cache entry inverseLabel table k f).integerBitBudget cache≤C*(p+1)^a)
    (hops : (inputTracedPairWord cache entry inverseLabel table k f).operations cache≤O*(p+1)^b) :
    (inputTracedPairWord cache entry inverseLabel table k f).numericalActions≤
      40000*(2*C+4)^2*O*(p+1)^(2*a+b) := by
  have hc:=inputTracedPairWord_numericalActions cache entry inverseLabel table k f (C*(p+1)^a) hbit
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
