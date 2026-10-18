import EffectiveEncoding.ProviderTerminal
import CircuitNumerical.RationalCacheBudgets

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 1000000


/-- All target-cache packets use heights derived from the actual descriptor. -/
def actualTargetCacheHeight (k L q : ℕ) : ℕ :=
  1000000*(k+3)^7*(cachePrecisionBudget L q+5)


theorem actualTargetCacheHeight_ge (k L q : ℕ) :
    cachePrecisionBudget L q+1≤actualTargetCacheHeight k L q := by
  have ha : 1≤1000000*(k+3)^7 := Nat.succ_le_of_lt (by positivity)
  have h := Nat.mul_le_mul_right (cachePrecisionBudget L q+5) ha
  unfold actualTargetCacheHeight
  omega


theorem actualTarget_PacketOracleHeight {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    PacketOracleHeight u.quaternionOracle (numericalDemand L (Nat.clog 2 (q+1)))
      (actualTargetCacheHeight k L q) := by
  intro r hr
  exact ⟨u.integerPacket r,u.integerPacket_value r,extractionCode_targetCache_height hu L q r hr⟩


theorem actualGate_PacketOracleHeight {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i)) (k L q : ℕ) (j : Fin m) :
    PacketOracleHeight (dyadicQuaternionOracle (entry j)) (numericalDemand L (Nat.clog 2 (q+1)))
      (actualTargetCacheHeight k L q) := by
  intro r hr
  refine ⟨dyadicIntegerPacket (entry j) r,dyadicIntegerPacket_value (entry j) r,?_⟩
  apply IntegerPacketHeight.mono _ _ _ (dyadicIntegerPacket_height (entry j) (G j) (he j) r)
  have hp : numericalDemand L (Nat.clog 2 (q+1))≤cachePrecisionBudget L q := numericalDemand_precision_bound L q
  exact (by omega : r+1≤cachePrecisionBudget L q+1).trans (actualTargetCacheHeight_ge k L q)


def actualDescriptorTraceBudget (n L k q : ℕ) : ℕ :=
  1000000000002*(n+1)*(4*(actualTargetCacheHeight k L q+1)+2)*(L+1)*traceRGrowth*(q+1)^128

/-- Every represented operand of the actual numerical trace now has an
internal target-height bound, derived from the actual extraction descriptor. -/

theorem actualDescriptorTrace_integerBitBudget {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (cachedArithmeticRun (fun j => dyadicQuaternionOracle (entry j)) inverseLabel table L q
      u.quaternionOracle).integerBitBudget≤actualDescriptorTraceBudget n L k q :=
  cachedArithmeticRun_rational_integerBitBudget _ inverseLabel table L q _ hL u.quaternionOracle
    (actualGate_PacketOracleHeight entry G he k L q) (actualTarget_PacketOracleHeight hu L q)


def actualTraceConstant (n L : ℕ) : ℕ :=
  1000000000002*(n+1)*(4000000*(51200000*(L+1)+5)+6)*(L+1)*traceRGrowth


theorem actualDescriptorTraceBudget_polynomial (n L k q : ℕ) :
    actualDescriptorTraceBudget n L k q≤actualTraceConstant n L*(k+3)^7*(q+1)^137 := by
  let X := (k+3)^7
  let Y := (q+1)^9
  have hx : 1≤X := Nat.succ_le_of_lt (by dsimp [X];positivity)
  have hy : 1≤Y := Nat.one_le_pow _ _ (by omega)
  have hp : cachePrecisionBudget L q+5≤(51200000*(L+1)+5)*Y := by
    unfold cachePrecisionBudget
    change 51200000*(L+1)*Y+5≤(51200000*(L+1)+5)*Y
    have h := Nat.mul_le_mul_left 5 hy
    nlinarith
  have hxy : 1≤X*Y := by simpa using Nat.mul_le_mul hx hy
  have hb : 4*(actualTargetCacheHeight k L q+1)+2≤
      (4000000*(51200000*(L+1)+5)+6)*X*Y := by
    calc
      _ = 4000000*X*(cachePrecisionBudget L q+5)+6 := by
        dsimp [X,actualTargetCacheHeight];ring
      _ ≤ 4000000*X*((51200000*(L+1)+5)*Y)+6*(X*Y) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hp) (by nlinarith)
      _ = _ := by ring
  have h := Nat.mul_le_mul_right ((L+1)*traceRGrowth*(q+1)^128)
    (Nat.mul_le_mul_left (1000000000002*(n+1)) hb)
  unfold actualDescriptorTraceBudget actualTraceConstant
  calc
    _ ≤ (1000000000002*(n+1)*((4000000*(51200000*(L+1)+5)+6)*X*Y))*
        ((L+1)*traceRGrowth*(q+1)^128) := by simpa only [Nat.mul_assoc] using h
    _ = _ := by
      dsimp [X,Y]
      generalize k+3=x
      generalize q+1=y
      rw [show 137=9+128 by decide,pow_add]
      ring


theorem actualDescriptorTrace_polynomial {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k) :
    (cachedArithmeticRun (fun j => dyadicQuaternionOracle (entry j)) inverseLabel table L q
      u.quaternionOracle).integerBitBudget≤actualTraceConstant n L*(k+3)^7*(q+1)^137 :=
  (actualDescriptorTrace_integerBitBudget entry G he inverseLabel table L q hL hu).trans
    (actualDescriptorTraceBudget_polynomial n L k q)


theorem actualDescriptorTrace_subtreeBound {m n k : ℕ}
    (entry : Fin m → DyadicQuaternionOracle) (G : Fin m → SU2)
    (he : ∀ i,DyadicQApproximates (entry i) (G i)) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L q : ℕ) (hL : ∀ j,(table j).length≤L)
    {i : Fin (originalWireCount k)} {u : SingleCode} (hu : GateCode.single i u∈extractionCode k)
    (e : ScalarExpression) (hmem : e∈(cachedArithmeticRun (fun j => dyadicQuaternionOracle (entry j))
      inverseLabel table L q u.quaternionOracle).expressions) :
    e.IntegerSubtreeBound (actualTraceConstant n L*(k+3)^7*(q+1)^137) :=
  ScalarExpression.integerSubtreeBound _ _
    ((List.le_sum_of_mem (List.mem_map.mpr ⟨e,hmem,rfl⟩)).trans
      (actualDescriptorTrace_polynomial entry G he inverseLabel table L q hL hu))

/-- A displayed polynomial of k, with no logarithm or actual circuit-size
oracle in its definition. Conservative degree is preferred here. -/

def actualGatePolynomial (k : ℕ) : ℕ :=
  20480*k*(k+2)^6*(6*(k+3)+2)^2+100*k^2


theorem extractionCode_length_polynomial (k : ℕ) : (extractionCode k).length≤actualGatePolynomial k := by
  have hlog : Nat.clog 2 (k+3)≤k+3 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  apply (extractionCode_polynomial_bound k).trans
  unfold actualGatePolynomial
  gcongr


def pipelinePrecisionPolynomial (k p : ℕ) : ℕ := p+2+actualGatePolynomial k


theorem extractionPrecision_polynomial (k p : ℕ) : extractionPrecision k p≤pipelinePrecisionPolynomial k p := by
  have hc : Nat.clog 2 (max 1 (extractionCode k).length)≤max 1 (extractionCode k).length :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=max 1 (extractionCode k).length)).le
  have hn := extractionCode_length_polynomial k
  unfold extractionPrecision dyadicCircuitPrecision pipelinePrecisionPolynomial
  omega

/-- One polynomial bound for target-provider subtree heights and the entire
numerical trace, at the actual precision requested by the extraction code. -/

def extractionOperandPolynomial (n L k p : ℕ) : ℕ :=
  actualTraceConstant n L*(k+3)^7*(pipelinePrecisionPolynomial k p+1)^137+
    1000000*(k+3)^7*(51200000*(L+1)*(pipelinePrecisionPolynomial k p+1)^9+5)


theorem extraction_provider_subtree_polynomial {n k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L p r : ℕ)
    (hr : r≤numericalDemand L (Nat.clog 2 (extractionPrecision k p+1))) :
    packetIntermediateHeights (u.packetExpression r) (extractionOperandPolynomial n L k p) := by
  apply packetIntermediateHeights_of_budget
  have h := (u.packetExpression_budget (extractionCode_fits k (.single i u) hu).1 r).trans
    (providerHeightBudget_polynomial k r)
  have hq := extractionPrecision_polynomial k p
  have hc : cachePrecisionBudget L (extractionPrecision k p)≤
      51200000*(L+1)*(pipelinePrecisionPolynomial k p+1)^9 := by
    unfold cachePrecisionBudget
    gcongr
  have hp := (hr.trans (numericalDemand_precision_bound L (extractionPrecision k p))).trans hc
  exact (h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 5))).trans
    (Nat.le_add_left _ _)



end EffectiveEncoding
