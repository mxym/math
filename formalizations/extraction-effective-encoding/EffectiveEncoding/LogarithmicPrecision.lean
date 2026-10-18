import EffectiveEncoding.PureIntegerBudgets

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- A logarithmic-in-register-size precision budget for the actual word. -/
def logarithmicPrecision (k p : ℕ) : ℕ := p+21+9*Nat.clog 2 (k+3)

theorem actualGatePolynomial_power_bound (k : ℕ) :
    actualGatePolynomial k≤2^20*(k+3)^9 := by
  let b:=k+3
  have hb : 1≤b := by omega
  have h29 : b^2≤b^9 := Nat.pow_le_pow_right hb (by decide)
  calc
    _≤20480*b*b^6*(7*b)^2+100*b^2 := by
      unfold actualGatePolynomial
      dsimp [b]
      gcongr <;> omega
    _≤20480*b*b^6*(7*b)^2+100*b^9 := Nat.add_le_add_left (Nat.mul_le_mul_left 100 h29) _
    _=1003620*b^9 := by ring
    _≤2^20*b^9 := Nat.mul_le_mul_right _ (by norm_num)


theorem extractionCode_length_power_bound (k : ℕ) :
    (extractionCode k).length≤2^(20+9*Nat.clog 2 (k+3)) := by
  have hb : k+3≤2^Nat.clog 2 (k+3) := Nat.le_pow_clog (by decide) _
  apply (extractionCode_length_polynomial k).trans
  apply (actualGatePolynomial_power_bound k).trans
  calc
    _≤2^20*(2^Nat.clog 2 (k+3))^9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 9)
    _=_ := by rw [← pow_mul,pow_add,Nat.mul_comm 9]


theorem extractionPrecision_logarithmic (k p : ℕ) :
    extractionPrecision k p≤logarithmicPrecision k p := by
  have hn:=extractionCode_length_power_bound k
  have hm : max 1 (extractionCode k).length≤2^(20+9*Nat.clog 2 (k+3)) :=
    max_le (Nat.one_le_pow _ _ (by decide)) hn
  have hc : Nat.clog 2 (max 1 (extractionCode k).length)≤20+9*Nat.clog 2 (k+3) :=
    Nat.clog_le_of_le_pow hm
  unfold extractionPrecision dyadicCircuitPrecision logarithmicPrecision
  omega


def rawLogarithmicOperandBudget (n L k p : ℕ) : ℕ :=
  2*(actualTraceConstant n L*(k+3)^7*(logarithmicPrecision k p+1)^137)


theorem rawExtraction_integerBitBudget_logarithmic {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (rawDescriptorRun entry inverseLabel table L (extractionPrecision k p) u).integerBitBudget≤
      rawLogarithmicOperandBudget n L k p := by
  apply (rawDescriptorRun_polynomial entry G he inverseLabel table L (extractionPrecision k p) hL hu).trans
  unfold rawLogarithmicOperandBudget
  gcongr
  exact extractionPrecision_logarithmic k p


theorem rawTargetCache_height_logarithmic {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L p r : ℕ)
    (hr : r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1))) :
    IntegerPacketHeight (u.rawPacket r)
      (1000000*(k+3)^7*(51200000*(L+1)*(logarithmicPrecision k p+1)^9+5)) := by
  apply IntegerPacketHeight.mono _ _ _ (extractionCode_rawPacket_height hu r)
  have hc := hr.trans (numericalDemand_precision_bound L (extractionPrecision k p))
  have hp : cachePrecisionBudget L (extractionPrecision k p)≤
      51200000*(L+1)*(logarithmicPrecision k p+1)^9 := by
    unfold cachePrecisionBudget
    gcongr
    exact extractionPrecision_logarithmic k p
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (hc.trans hp) 5)

end EffectiveEncoding
