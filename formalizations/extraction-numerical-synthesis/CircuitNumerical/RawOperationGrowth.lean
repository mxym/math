import CircuitNumerical.RawOperationRecursion
import CircuitNumerical.RawIntegerPacketExpressions

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem rawCorrectionOperationOffset_le (A B D L M : ℕ) (hB : B≤D) (hL : 68*L≤49*M) :
    rawCorrectionOperationOffset A B L≤correctionOperationOffset A D M := by
  have h:=Nat.mul_le_mul_left (100000*A) hL
  unfold rawCorrectionOperationOffset correctionOperationOffset
  nlinarith

theorem rawPairOperationOffset_le (n L k : ℕ) :
    rawPairOperationOffset n L k≤pairOperationOffset n (2*L) k := by
  induction k with
  | zero => simp only [rawPairOperationOffset,pairOperationOffset];nlinarith
  | succ k ih =>
    have hL : 68*(L*25^k)≤49*((2*L)*25^k) := by
      have h:=Nat.mul_le_mul_right (L*25^k) (by decide : 68≤98)
      convert h using 1 <;> ring
    have hM : 68*(5*(L*25^k))≤49*(5*((2*L)*25^k)) := by
      have h:=Nat.mul_le_mul_left 5 hL
      convert h using 1 <;> ring
    have hi:=rawCorrectionOperationOffset_le (pairOperationSlope n k) _ _ _ _ ih hL
    exact rawCorrectionOperationOffset_le _ _ _ _ _ hi hM

theorem tracedPairWord_twenty_operations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 20) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : PacketExpressionOracle) (hf : PacketOperationBound f 20) :
    (tracedPairWord entry inverseLabel table k f).operations≤1020*(n+1)*(2*L+1)*offsetGrowth^k := by
  have h:=rawTracedPairWord_operations entry he inverseLabel table L hL k f 20 hf
  have ha:=pairOperationSlope_bound n k
  have hb:=(rawPairOperationOffset_le n L k).trans (pairOperationOffset_bound n (2*L) k)
  have hp : slopeGrowth^k≤offsetGrowth^k := Nat.pow_le_pow_left (by norm_num [slopeGrowth,offsetGrowth]) k
  have hA : pairOperationSlope n k≤(n+1)*offsetGrowth^k := ha.trans (Nat.mul_le_mul_left _ hp)
  nlinarith

theorem tracedPairWord_twenty_precision_operations {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 20) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : PacketExpressionOracle) (hf : PacketOperationBound f 20) :
    (tracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).operations≤
      (1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64 := by
  have h:=tracedPairWord_twenty_operations entry he inverseLabel table L (Nat.clog 2 (p+1)) hL f hf
  exact h.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (1020*(n+1)*(2*L+1)) (offsetGrowth_precision_bound p))

theorem rawPacketExpressionOracle_operationBound (f : ℕ → IntegerPacket) :
    PacketOperationBound (rawPacketExpressionOracle f) 20 := by
  intro p
  rw [rawPacketExpressionOracle,rawPacketExpression_operations]

theorem costedRawPacketPairWord_operations {m n : ℕ} (entry : Fin m → ℕ → IntegerPacket)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : ℕ → IntegerPacket) :
    (costedTracedPairWord (fun i => rawPacketExpressionOracle (entry i)) inverseLabel table
      (Nat.clog 2 (p+1)) (rawPacketExpressionOracle f)).result.operations≤
        (1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64 := by
  rw [costedTracedPairWord_result]
  exact tracedPairWord_twenty_precision_operations _
    (fun i => rawPacketExpressionOracle_operationBound (entry i)) inverseLabel table L p hL _
    (rawPacketExpressionOracle_operationBound f)

theorem costedTracedPairWord_twenty_rootCharge {m n : ℕ} (entry : Fin m → PacketExpressionOracle)
    (he : ∀ i,PacketOperationBound (entry i) 20) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L p B : ℕ) (hL : ∀ j,(table j).length≤L)
    (f : PacketExpressionOracle) (hf : PacketOperationBound f 20)
    (heB : ∀ i,PacketBitEnvelope (entry i) (0,B)) (hfB : PacketBitEnvelope f (0,B)) :
    let C:=1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128
    (costedTracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f).rootCharge≤
      (16*(C+2)+5)*((1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64) := by
  dsimp only
  let r:=costedTracedPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f
  let C:=1000000000002*(n+1)*(B+2)*(L+1)*traceRGrowth*(p+1)^128
  have hbit : r.result.integerBitBudget≤C := by
    rw [costedTracedPairWord_result]
    have h:=tracedPairWord_flat_integerBitBudget entry B heB inverseLabel table L (Nat.clog 2 (p+1)) hL f hfB
    exact h.trans (by simpa only [C,Nat.mul_assoc] using
      Nat.mul_le_mul_left (1000000000002*(n+1)*(B+2)*(L+1)) (traceRGrowth_precision_bound p))
  have hops : r.result.operations≤(1020*(n+1)*(2*L+1)*offsetGrowth)*(p+1)^64 := by
    rw [costedTracedPairWord_result]
    exact tracedPairWord_twenty_precision_operations entry he inverseLabel table L p hL f hf
  exact ((costedTracedPairWord_rootCharge entry inverseLabel table _ f).trans
    (ArithmeticWordResult.binaryRootPrimitiveOperations_bound r.result C hbit)).trans
      (Nat.mul_le_mul_left _ hops)

end CircuitRecursion
