import CircuitNumerical.NativePolynomialPower
import CircuitNumerical.RawOperationGrowth

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

abbrev nativeWordDataExpression (f : NativePacketDataOracle) : NativePacketExpressionOracle := fun q => .literal (f q)

theorem nativeWordData_refines (f : NativePacketDataOracle) :
    NativePacketOracleRefines (nativeWordDataExpression f) (rawPacketExpressionOracle (fun q => (f q).decode)) :=
  fun q => NativePacketRefines.raw (f q)

theorem nativeDataPairWord_integerBitBudget {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k A : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle)
    (he : ∀ i r,IntegerPacketHeight (entry i r).decode A) (hf : ∀ r,IntegerPacketHeight (f r).decode A) :
    (nativeTracedPairWord (fun i => nativeWordDataExpression (entry i)) inverseLabel table k
      (nativeWordDataExpression f)).integerBitBudget≤
      20*(1000000000002*(n+1)*(8*(A+1)+2)*(L+1)*traceRGrowth^k) := by
  have href:=nativeTracedPairWord_refines (entry:=fun i => nativeWordDataExpression (entry i))
    (E:=fun i => rawPacketExpressionOracle (fun q => (entry i q).decode))
    (fun i => nativeWordData_refines (entry i)) inverseLabel table k (f:=nativeWordDataExpression f)
    (F:=rawPacketExpressionOracle (fun q => (f q).decode)) (nativeWordData_refines f)
  have hbit:=tracedPairWord_flat_integerBitBudget (fun i => rawPacketExpressionOracle (fun q => (entry i q).decode))
    (8*(A+1)) (fun i => rawPacketExpressionOracle_bitEnvelope (fun q => (entry i q).decode) A (he i))
    inverseLabel table L k hL (rawPacketExpressionOracle (fun q => (f q).decode))
    (rawPacketExpressionOracle_bitEnvelope (fun q => (f q).decode) A hf)
  exact href.budget_le.trans (Nat.mul_le_mul_left 20 hbit)

theorem nativeDataPairWord_operations {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k : ℕ) (hL : ∀ j,(table j).length≤L) (f : NativePacketDataOracle) :
    (nativeTracedPairWord (fun i => nativeWordDataExpression (entry i)) inverseLabel table k
      (nativeWordDataExpression f)).operations≤20*(1020*(n+1)*(2*L+1)*offsetGrowth^k) := by
  have href:=nativeTracedPairWord_refines (entry:=fun i => nativeWordDataExpression (entry i))
    (E:=fun i => rawPacketExpressionOracle (fun q => (entry i q).decode))
    (fun i => nativeWordData_refines (entry i)) inverseLabel table k (f:=nativeWordDataExpression f)
    (F:=rawPacketExpressionOracle (fun q => (f q).decode)) (nativeWordData_refines f)
  have hops:=tracedPairWord_twenty_operations (fun i => rawPacketExpressionOracle (fun q => (entry i q).decode))
    (fun i => rawPacketExpressionOracle_operationBound _) inverseLabel table L k hL
    (rawPacketExpressionOracle (fun q => (f q).decode)) (rawPacketExpressionOracle_operationBound _)
  exact href.operations_le.trans (Nat.mul_le_mul_left 20 hops)

end CircuitRecursion
