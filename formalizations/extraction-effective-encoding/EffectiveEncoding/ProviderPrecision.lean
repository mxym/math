import EffectiveEncoding.ProviderExpressions

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 800000

/-- Maximum integer-sqrt precision in a closed expression, charging all
branches. These measures inspect the actual finite expression syntax. -/
def fourMax (f : Fin 4 → ℕ) : ℕ := max (f 0) (max (f 1) (max (f 2) (f 3)))

mutual
def scalarRootPrecision : ScalarExpression → ℕ
  | .literal _ | .stoppingThreshold _ => 0
  | .add a b | .mul a b => max (scalarRootPrecision a) (scalarRootPrecision b)
  | .neg a | .inv a | .meanMinus a => scalarRootPrecision a
  | .sqrt a p => max p (scalarRootPrecision a)
  | .coordinate a _ => packetRootPrecision a
  | .distance a b => max (packetRootPrecision a) (packetRootPrecision b)
def packetRootPrecision : PacketExpression → ℕ
  | .literal _ => 0
  | .tuple a => fourMax (fun i => scalarRootPrecision (a i))
  | .mul a b => max (packetRootPrecision a) (packetRootPrecision b)
  | .inverse a => packetRootPrecision a
  | .selectMax scores branches => max (fourMax (fun i => scalarRootPrecision (scores i)))
      (fourMax (fun i => packetRootPrecision (branches i)))
end

theorem fourMax_le (f : Fin 4 → ℕ) (B : ℕ) (h : ∀ i,f i≤B) : fourMax f≤B := by
  exact max_le (h 0) (max_le (h 1) (max_le (h 2) (h 3)))

theorem halfCosExpression_precision (n : ℕ) (f : ScalarExpressionOracle)
    (hf : ∀ p,scalarRootPrecision (f p)≤p+1) (p : ℕ) :
    scalarRootPrecision (halfCosExpression n f p)≤2^n*(p+2) := by
  induction n generalizing p with
  | zero => simpa only [halfCosExpression,pow_zero,one_mul] using (hf p).trans (by omega)
  | succ n ih =>
    have h := ih (2*p+2)
    simp only [halfCosExpression,expressionSqrt,meanPlusExpression,scalarRootPrecision,
      zero_le,max_eq_right]
    apply max_le
    · have hp : 1≤2^(n+1) := Nat.one_le_pow _ _ (by decide)
      nlinarith
    · convert h using 1 <;> first | rfl | rw [pow_succ];ring

theorem halfSinExpression_precision (n : ℕ) (f g : ScalarExpressionOracle)
    (hf : ∀ p,scalarRootPrecision (f p)≤p+1) (hg : ∀ p,scalarRootPrecision (g p)≤p+1)
    (p : ℕ) : scalarRootPrecision (halfSinExpression n f g p)≤2^n*(p+2) := by
  cases n with
  | zero => simpa only [halfSinExpression,pow_zero,one_mul] using (hg p).trans (by omega)
  | succ n =>
    have h := halfCosExpression_precision n f hf (2*p+2)
    simp only [halfSinExpression,expressionSqrt,expressionMeanMinus,scalarRootPrecision]
    apply max_le
    · have hp : 1≤2^(n+1) := Nat.one_le_pow _ _ (by decide)
      nlinarith
    · convert h using 1 <;> first | rfl | rw [pow_succ];ring

theorem AngleAtom.expression_precision (a : AngleAtom) (p : ℕ) :
    scalarRootPrecision (a.cosExpression p)≤p+1 ∧
    scalarRootPrecision (a.sinExpression p)≤p+1 := by
  cases a with
  | pi => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | merge A B j =>
    simp only [cosExpression,sinExpression]
    split_ifs <;> simp [expressionSqrt,constantExpression,scalarRootPrecision]

theorem AngleCode.expression_precision (a : AngleCode) (p : ℕ) :
    scalarRootPrecision (a.cosExpression p)≤2^a.halvings*(p+2) ∧
    scalarRootPrecision (a.sinExpression p)≤2^a.halvings*(p+2) := by
  have hc := halfCosExpression_precision a.halvings a.atom.cosExpression
    (fun q => (a.atom.expression_precision q).1) p
  have hs := halfSinExpression_precision a.halvings a.atom.cosExpression a.atom.sinExpression
    (fun q => (a.atom.expression_precision q).1) (fun q => (a.atom.expression_precision q).2) p
  constructor
  · exact hc
  · cases hn : a.negative <;>
      simpa only [sinExpression,hn,expressionNeg,Bool.false_eq_true,if_false,if_true,scalarRootPrecision] using hs

theorem SingleCode.packetExpression_precision {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    packetRootPrecision (u.packetExpression p)≤2^(H+1)*(p+5) := by
  induction u with
  | hadamard =>
    have hp : 1≤2^(H+1) := Nat.one_le_pow _ _ (by decide)
    simp [packetExpression,packetRootPrecision,fourMax,scalarRootPrecision]
    nlinarith
  | yBasis => simp [packetExpression,packetRootPrecision,fourMax,scalarRootPrecision]
  | phase a b =>
    have hca := ((a.half 1).expression_precision (p+3)).1
    have hsa := ((a.half 1).expression_precision (p+3)).2
    have hcb := ((b.half 1).expression_precision (p+3)).1
    have hsb := ((b.half 1).expression_precision (p+3)).2
    have ha : 2^(a.half 1).halvings*(p+5)≤2^(H+1)*(p+5) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right h.1.2 1))
    have hb : 2^(b.half 1).halvings*(p+5)≤2^(H+1)*(p+5) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right h.2.2 1))
    have hca' := hca.trans ha
    have hsa' := hsa.trans ha
    have hcb' := hcb.trans hb
    have hsb' := hsb.trans hb
    simp [packetExpression,packetRootPrecision,fourMax,scalarRootPrecision,phaseCosExpression,
      phaseSinExpression,expressionAdd,expressionMul,expressionNeg,Nat.add_assoc,
      max_le_iff,hca',hsa',hcb',hsb']
  | inverse u ih => exact ih h

/-- The conservative logarithmic halving envelope still gives a polynomial
precision amplification. -/
theorem halvingBudget_power (k : ℕ) : 2^halvingBudget k≤256*(k+3)^6 := by
  have hx : 1<k+3 := by omega
  have hc : 0<Nat.clog 2 (k+3) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by change 1<k+3;omega)
  have hp := Nat.pow_pred_clog_lt_self (b:=2) (by decide) hx
  simp only [Nat.pred_eq_sub_one] at hp
  have he : 2^Nat.clog 2 (k+3)=2^(Nat.clog 2 (k+3)-1)*2 := by
    rw [← pow_succ]
    congr 1 <;> omega
  have hb : 2^Nat.clog 2 (k+3)≤2*(k+3) := by rw [he];nlinarith
  have h6 := Nat.pow_le_pow_left hb 6
  calc
    2^halvingBudget k=(2^Nat.clog 2 (k+3))^6*4 := by
      unfold halvingBudget
      rw [pow_add,show 6*Nat.clog 2 (k+3)=Nat.clog 2 (k+3)*6 by omega,pow_mul]
      norm_num
    _ ≤ (2*(k+3))^6*4 := Nat.mul_le_mul_right 4 h6
    _ = 256*(k+3)^6 := by ring

theorem binaryWidth_le (k : ℕ) : binaryWidth k≤k+1 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+1)).le

theorem providerHeightBudget_polynomial (k p : ℕ) :
    providerHeightBudget (4*k) (halvingBudget k) p≤1000000*(k+3)^7*(p+5) := by
  have hlog : Nat.clog 2 (k+3)≤k+3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hw := binaryWidth_le (4*k)
  have hb : binaryWidth (4*k)+3+8*(halvingBudget k+1+1)≤60*(k+3) := by
    unfold halvingBudget
    omega
  have hp : 2^(halvingBudget k+1+1)≤1024*(k+3)^6 := by
    have h := Nat.mul_le_mul_right 4 (halvingBudget_power k)
    rw [pow_succ,pow_succ]
    nlinarith
  have h := Nat.add_le_add_right (Nat.mul_le_mul_right (p+5)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hb) hp)) 4
  have he : 8*(60*(k+3))*(1024*(k+3)^6)*(p+5)+4≤1000000*(k+3)^7*(p+5) := by
    let X := (k+3)^7*(p+5)
    have hpos : 1≤X := Nat.succ_le_of_lt (by dsimp [X];positivity)
    calc
      _ = 491520*X+4 := by dsimp [X];ring
      _ ≤ 1000000*X := by omega
      _ = _ := by dsimp [X];ring
  unfold providerHeightBudget halfExpressionBudget
  calc
    _ ≤ 8*(60*(k+3))*(1024*(k+3)^6)*(p+5)+4 := by
      simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.mul_assoc] using h
    _ ≤ _ := he

theorem extractionCode_provider_precision {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    packetRootPrecision (u.packetExpression p)≤512*(k+3)^6*(p+5) := by
  have h := (extractionCode_fits k (.single i u) hu).1
  have hs := u.packetExpression_precision h p
  have hp := Nat.mul_le_mul_right 2 (halvingBudget_power k)
  rw [← pow_succ] at hp
  have hp' : 2^(halvingBudget k+1)≤512*(k+3)^6 := by
    convert hp using 1 <;> ring
  exact hs.trans (Nat.mul_le_mul_right _ hp')

theorem extractionCode_provider_integerHeight {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    IntegerPacketHeight (u.integerPacket p) (1000000*(k+3)^7*(p+5)) :=
  IntegerPacketHeight.mono _ _ _
    (u.integerPacket_height (extractionCode_fits k (.single i u) hu).1 p)
    (providerHeightBudget_polynomial k p)

/-- Eager target-cache construction evaluates these actual closed packet
expressions at each requested precision, once per stored entry. -/
def targetCacheOperations (u : SingleCode) (L q : ℕ) : ℕ :=
  ∑ r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1),(u.packetExpression r.val).operations

theorem extractionCode_targetCache_operations {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    targetCacheOperations u L q≤(cachePrecisionBudget L q+1)*(100*(halvingBudget k+3)+4) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun (r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1)) _ =>
      (extractionCode_provider_resources hu r.val).1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  exact hs.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (numericalDemand_precision_bound L q) 1))

theorem extractionCode_targetCache_precision {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q r : ℕ)
    (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) :
    packetRootPrecision (u.packetExpression r)≤512*(k+3)^6*(cachePrecisionBudget L q+5) :=
  (extractionCode_provider_precision hu r).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hr.trans (numericalDemand_precision_bound L q)) 5))

theorem extractionCode_targetCache_height {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q r : ℕ)
    (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) :
    IntegerPacketHeight (u.integerPacket r)
      (1000000*(k+3)^7*(cachePrecisionBudget L q+5)) :=
  IntegerPacketHeight.mono _ _ _ (extractionCode_provider_integerHeight hu r)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hr.trans (numericalDemand_precision_bound L q)) 5))

def gateTargetCacheOperations {n : ℕ} (L q : ℕ) : GateCode n → ℕ
  | .single _ u => targetCacheOperations u L q
  | .cnot _ _ _ => 0

def extractionTargetCacheOperations (L k p : ℕ) : ℕ :=
  ((extractionCode k).map (gateTargetCacheOperations L (extractionPrecision k p))).sum

theorem extractionTargetCacheOperations_bound (L k p : ℕ) :
    extractionTargetCacheOperations L k p≤(extractionCode k).length*
      ((cachePrecisionBudget L (extractionPrecision k p)+1)*(100*(halvingBudget k+3)+4)) := by
  unfold extractionTargetCacheOperations
  calc
    _ ≤ ((extractionCode k).map (fun _ =>
        (cachePrecisionBudget L (extractionPrecision k p)+1)*(100*(halvingBudget k+3)+4))).sum := by
      apply List.sum_le_sum
      intro g hg
      cases g with
      | single i u => exact extractionCode_targetCache_operations hg L _
      | cnot c t h => exact Nat.zero_le _
    _ = _ := by simp

end EffectiveEncoding
