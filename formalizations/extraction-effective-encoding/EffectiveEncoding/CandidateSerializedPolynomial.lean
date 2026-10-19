import EffectiveEncoding.CandidateSerializedCosts

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Algebraic comparison of numeric envelopes only. It does not identify
execution records from different descriptor generators. -/
theorem candidateBudget_add_algebra (G S R N A T O B : ℕ) :
    G+N*(A+T)+O+B≤G+((S+(R+N*A))+N*T)+O+B := by
  rw [Nat.mul_add]
  omega


theorem candidateSerializedPrimitiveBudget_enlarge (m n L k p gateB : ℕ) :
    candidateSerializedPrimitiveBudget m n L k p gateB≤
      3506*k*(k+5)^9+serializedPrimitiveBudget m n L k p gateB := by
  dsimp only [candidateSerializedPrimitiveBudget,serializedPrimitiveBudget]
  have h:=candidateBudget_add_algebra (3506*k*(k+5)^9) (1800*k*(k+3)^8)
    (306*k*(k+4)^9) (actualGatePolynomial k)
    ((200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*(k+3)^15+
      actualInputOnlineCoefficient m n L k gateB)*(logarithmicPrecision k p+1)^338)
    ((8192*(L+2*(n+1)+2))*(logarithmicPrecision k p+1)^13)
    (actualGatePolynomial k*(12*(32*L*(logarithmicPrecision k p+1)^5+2))+1)
    (outputLabelBudget k L p*(90*(labelFieldWidth m (originalWireCount k)+1)^2)+2)
  simpa only [Nat.mul_assoc,Nat.add_assoc] using h


theorem candidateGeneration_uniform (k p : ℕ) :
    3506*k*(k+5)^9≤(3506*2^9)*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  generalize hbdef : k+3=b
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  have hk : k≤b := by omega
  have h5 : k+5≤2*b := by omega
  calc
    _≤3506*b*(2*b)^9 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) (Nat.pow_le_pow_left h5 9)
    _=(3506*2^9)*b^10 := by ring
    _≤_ := by
      simpa only [pow_zero,Nat.mul_one] using
        serializedMonomial_le b Q (3506*2^9) 10 0 24 338 hb hQ (by decide) (by decide)


def candidateSerializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  3506*2^9+serializedPolynomialConstant m n L gateB

/-- The new actual program's explicit numeric envelope has the same uniform
24/338 degrees. All coefficient dependence on k is proved internally. -/
theorem candidateSerializedPrimitiveBudget_polynomial (m n L k p gateB : ℕ) :
    candidateSerializedPrimitiveBudget m n L k p gateB≤
      candidateSerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  apply (candidateSerializedPrimitiveBudget_enlarge m n L k p gateB).trans
  exact (Nat.add_le_add (candidateGeneration_uniform k p)
    (serializedPrimitiveBudget_polynomial m n L k p gateB)).trans_eq (by
      unfold candidateSerializedPolynomialConstant
      rw [Nat.add_mul,Nat.add_mul])

/-- Actual retained generation/target/numeric/read/assembly/materialization/
Boolean-output execution, with only the fixed-library queried height contract.
This specified partial primitive bound is not a whole-machine runtime claim. -/
theorem candidateSerializedRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (candidateSerializedRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      candidateSerializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 :=
  (candidateSerializedRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he).trans
    (candidateSerializedPrimitiveBudget_polynomial m n L k p gateB)

end EffectiveEncoding
