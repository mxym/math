import EffectiveEncoding.SerializedCoefficientBounds

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Elementary comparison of monomials; used only to collect the already
specified primitive models in one uniform bound. -/
theorem serializedMonomial_le (b Q c i j I J : ℕ) (hb : 1≤b) (hQ : 1≤Q)
    (hi : i≤I) (hj : j≤J) :
    c*b^i*Q^j≤c*b^I*Q^J :=
  Nat.mul_le_mul (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hb hi))
    (Nat.pow_le_pow_right hQ hj)

/-- Explicit constant depending only on the fixed library parameters.  Every
k-dependent coefficient of the actual retained model is bounded internally. -/
def serializedPolynomialConstant (m n L gateB : ℕ) : ℕ :=
  1800+306*2^9+
  2^20*(3200+nativeProviderCachePolynomialConstant L+actualInputOnlineCoefficient m n L 0 gateB)+
  2^20*(8192*(L+2*(n+1)+2))+
  2^20*12*(32*L+2)+1+
  2^20*(32*L+1)*90*(m+2)^2+2

/-- Uniform polynomial for the concrete serializer's accounted primitive
budget. This is a theorem about the specified partial operation models, not a
claim that output length accounts for construction or full machine time. -/
theorem serializedPrimitiveBudget_polynomial (m n L k p gateB : ℕ) :
    serializedPrimitiveBudget m n L k p gateB≤
      serializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 := by
  have hn:=actualGatePolynomial_power_bound k
  have hp:=preparationCoefficient_polynomial k
  have hc:=actualInputOnlineCoefficient_polynomial m n L k gateB
  have hw:=labelFieldWidth_polynomial m k
  dsimp only [serializedPrimitiveBudget,outputLabelBudget]
  generalize hbdef : k+3=b at hn hp hc hw ⊢
  generalize hQdef : logarithmicPrecision k p+1=Q
  have hb : 1≤b := by omega
  have hQ : 1≤Q := by omega
  have hk : k≤b := by omega
  have h4 : k+4≤2*b := by omega
  have hunit : 1≤b^24*Q^338 := Nat.mul_le_mul
    (Nat.one_le_pow _ _ hb) (Nat.one_le_pow _ _ hQ)
  have hscan : 1800*k*b^8≤1800*b^24*Q^338 := by
    calc
      _≤1800*b*b^8 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
      _=1800*b^9 := by ring
      _≤1800*b^24*Q^338 := by
        simpa only [pow_zero,Nat.mul_one] using
          serializedMonomial_le b Q 1800 9 0 24 338 hb hQ (by decide) (by decide)
  have hrank : 306*k*(k+4)^9≤(306*2^9)*b^24*Q^338 := by
    calc
      _≤306*b*(2*b)^9 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) (Nat.pow_le_pow_left h4 9)
      _=(306*2^9)*b^10 := by ring
      _≤(306*2^9)*b^24*Q^338 := by
        simpa only [pow_zero,Nat.mul_one] using
          serializedMonomial_le b Q (306*2^9) 10 0 24 338 hb hQ (by decide) (by decide)
  have hinner : 200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*b^15+
      actualInputOnlineCoefficient m n L k gateB≤
      (3200+nativeProviderCachePolynomialConstant L+actualInputOnlineCoefficient m n L 0 gateB)*b^15 := by
    have hp' := hp.trans (Nat.mul_le_mul_left 3200 (Nat.pow_le_pow_right hb (show 2≤15 by decide)))
    have hc' := hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (show 14≤15 by decide)))
    exact (Nat.add_le_add (Nat.add_le_add_right hp' _) hc').trans_eq (by ring)
  have hcore : actualGatePolynomial k*(200*(4*k+2)^2+nativeProviderCachePolynomialConstant L*b^15+
      actualInputOnlineCoefficient m n L k gateB)*Q^338≤
      (2^20*(3200+nativeProviderCachePolynomialConstant L+actualInputOnlineCoefficient m n L 0 gateB))*b^24*Q^338 := by
    calc
      _≤(2^20*b^9)*((3200+nativeProviderCachePolynomialConstant L+
          actualInputOnlineCoefficient m n L 0 gateB)*b^15)*Q^338 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hn hinner)
      _=_ := by ring
  have hassembly : actualGatePolynomial k*((8192*(L+2*(n+1)+2))*Q^13)≤
      (2^20*(8192*(L+2*(n+1)+2)))*b^24*Q^338 := by
    calc
      _≤(2^20*b^9)*((8192*(L+2*(n+1)+2))*Q^13) := Nat.mul_le_mul_right _ hn
      _=(2^20*(8192*(L+2*(n+1)+2)))*b^9*Q^13 := by ring
      _≤_ := serializedMonomial_le b Q _ 9 13 24 338 hb hQ (by decide) (by decide)
  have hQ5 : 1≤Q^5 := Nat.one_le_pow _ _ hQ
  have hsum2 : 32*L*Q^5+2≤(32*L+2)*Q^5 := by nlinarith
  have houter : actualGatePolynomial k*(12*(32*L*Q^5+2))+1≤
      (2^20*12*(32*L+2)+1)*b^24*Q^338 := by
    have hmain : actualGatePolynomial k*(12*(32*L*Q^5+2))≤
        (2^20*12*(32*L+2))*b^24*Q^338 := by
      calc
        _≤(2^20*b^9)*(12*((32*L+2)*Q^5)) := Nat.mul_le_mul hn (Nat.mul_le_mul_left 12 hsum2)
        _=(2^20*12*(32*L+2))*b^9*Q^5 := by ring
        _≤_ := serializedMonomial_le b Q _ 9 5 24 338 hb hQ (by decide) (by decide)
    exact (Nat.add_le_add hmain hunit).trans_eq (by ring)
  have hsum1 : 32*L*Q^5+1≤(32*L+1)*Q^5 := by nlinarith
  have hstream : actualGatePolynomial k*(32*L*Q^5+1)*
      (90*(labelFieldWidth m (originalWireCount k)+1)^2)+2≤
      (2^20*(32*L+1)*90*(m+2)^2+2)*b^24*Q^338 := by
    have hmain : actualGatePolynomial k*(32*L*Q^5+1)*
        (90*(labelFieldWidth m (originalWireCount k)+1)^2)≤
        (2^20*(32*L+1)*90*(m+2)^2)*b^24*Q^338 := by
      calc
        _≤(2^20*b^9)*((32*L+1)*Q^5)*(90*((m+2)*b)^2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn hsum1) (Nat.mul_le_mul_left 90 (Nat.pow_le_pow_left hw 2))
        _=(2^20*(32*L+1)*90*(m+2)^2)*b^11*Q^5 := by ring
        _≤_ := serializedMonomial_le b Q _ 11 5 24 338 hb hQ (by decide) (by decide)
    have htwo : 2≤2*(b^24*Q^338) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hunit
    exact (Nat.add_le_add hmain htwo).trans_eq (by ring)
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hscan (Nat.add_le_add hrank hcore))
    hassembly) houter) hstream).trans_eq (by unfold serializedPolynomialConstant;ring)

/-- The actual serialized extraction execution satisfies the uniform bound.
Only the fixed-library queried packet-height contract is supplied; target
provider, retained numerical/read/assembly records, rank traces and output
encoding are the concrete programs already proved above. -/
theorem serializedInputRun_accountedPrimitiveActions_polynomial {m n : ℕ}
    (entry : Fin m → NativePacketDataOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p gateB : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i r,r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1)) →
      IntegerPacketHeight (entry i r).decode (gateB*(extractionPrecision k p+1)^9)) :
    (serializedInputRun entry inverseLabel table L k p).accountedPrimitiveActions≤
      serializedPolynomialConstant m n L gateB*(k+3)^24*(logarithmicPrecision k p+1)^338 :=
  (serializedInputRun_accountedPrimitiveActions entry inverseLabel table L k p gateB hL he).trans
    (serializedPrimitiveBudget_polynomial m n L k p gateB)

end EffectiveEncoding
