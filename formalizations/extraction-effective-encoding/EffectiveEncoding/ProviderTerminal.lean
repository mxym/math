import EffectiveEncoding.ProviderIntermediateHeights
import CircuitNumerical.FactorBitBudgets

open scoped BigOperators Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- These are the actual integer packets computed while materializing the
finite target cache, rather than an opaque oracle with a supplied cost law. -/
def integerTargetCache (u : SingleCode) (L q : ℕ) :
    List.Vector IntegerPacket (numericalDemand L (Nat.clog 2 (q+1))+1) :=
  List.Vector.ofFn (fun r => u.integerPacket r.val)

theorem integerTargetCache_values (u : SingleCode) (L q : ℕ) :
    (integerTargetCache u L q).map IntegerPacket.value=
      (buildPacketCache u.quaternionOracle (numericalDemand L (Nat.clog 2 (q+1)))).1 := by
  apply List.Vector.ext
  intro r
  simp [integerTargetCache,buildPacketCache,SingleCode.integerPacket_value]

/-- A concrete backend variant of the actual descriptor compiler. Its target
cache is constructed by the closed IntegerScalar/IntegerPacket execution. -/
def integerDescriptorSynthesis {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : List (Fin m) :=
  let depth := Nat.clog 2 (q+1)
  let P := numericalDemand L depth
  let gates := List.Vector.ofFn (fun i : Fin m => buildPacketCache (entry i) P)
  let target := integerTargetCache u L q
  (tracedPairWord (fun i r => .literal (readPacketCache (gates.get i).1 r)) inverseLabel table
    depth (fun r => .literal (readPacketCache (target.map IntegerPacket.value) r))).word

/-- Backend substitution preserves the literal emitted library-label word. -/
theorem integerDescriptorSynthesis_eq {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) :
    integerDescriptorSynthesis entry inverseLabel table L q u=
      descriptorSynthesis entry inverseLabel table L q u := by
  simp only [integerDescriptorSynthesis,integerTargetCache_values,descriptorSynthesis,cachedArithmeticRun]

def integerNumericalExtractionCode {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w := extractionCode k
  let q := dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (integerDescriptorSynthesis entry inverseLabel table L q) w

theorem integerNumericalExtractionCode_eq {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    integerNumericalExtractionCode entry inverseLabel table L k p=
      numericalExtractionCode entry inverseLabel table L k p := by
  dsimp only [integerNumericalExtractionCode,numericalExtractionCode]
  apply congrArg (fun f => compileLabelWord f (extractionCode k))
  funext u
  exact integerDescriptorSynthesis_eq entry inverseLabel table L _ u

theorem integerNumericalExtractionCode_error {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576) (k p : ℕ) :
    ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-wordPhase (extractionCode k) •
        (denote (labelCircuit G (integerNumericalExtractionCode entry inverseLabel table L k p)) :
          Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤
            (1/2:ℝ)^(p+1) := by
  rw [integerNumericalExtractionCode_eq]
  exact numericalExtractionCode_error G entry he inverseLabel hi table L hL hcover k p

theorem integerNumericalExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤
      (Extraction.bellProjector (d := Bits (bellPairYield k))*
        approximateExtractionOutput k
          (denote (labelCircuit G (integerNumericalExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [integerNumericalExtractionCode_eq]
  exact numericalExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

/-- Signed numerator widths and common denominator width of an actually
stored packet. Constructor delimiters and heap allocation are separate. -/
def integerPacketBits (a : IntegerPacket) : ℕ :=
  (binaryWidth a.denominator+1)+∑ i : Fin 4,(binaryWidth (a.numerators.get i).natAbs+1)

theorem integerPacketBits_bound (a : IntegerPacket) (B : ℕ) (h : IntegerPacketHeight a B) :
    integerPacketBits a≤5*(B+2) := by
  have hd := h.binary_bounds a B
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => hd.2 i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  unfold integerPacketBits binaryWidth
  omega

def integerTargetCacheBits (u : SingleCode) (L q : ℕ) : ℕ :=
  ∑ r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1),
    integerPacketBits ((integerTargetCache u L q).get r)

theorem extractionCode_integerTargetCacheBits {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    integerTargetCacheBits u L q≤(cachePrecisionBudget L q+1)*
      (5*(1000000*(k+3)^7*(cachePrecisionBudget L q+5)+2)) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun (r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1)) _ =>
      integerPacketBits_bound (u.integerPacket r.val) _
        (extractionCode_targetCache_height hu L q r.val (by omega)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have h : integerTargetCacheBits u L q≤
      (numericalDemand L (Nat.clog 2 (q+1))+1)*
        (5*(1000000*(k+3)^7*(cachePrecisionBudget L q+5)+2)) := by
    simpa only [integerTargetCacheBits,integerTargetCache,List.Vector.get_ofFn] using hs
  exact h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (numericalDemand_precision_bound L q) 1))

/-- The original traced numerical-word arithmetic plus the actual target
cache provider expressions; fixed-library provider execution is still a
separate input cost. This is an expression charge, not Turing time. -/
def extractionWithTargetOperations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : ℕ :=
  extractionArithmeticOperations entry inverseLabel table L k p+
    extractionTargetCacheOperations L k p

theorem extractionWithTargetOperations_bound {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionWithTargetOperations entry inverseLabel table L k p≤
      (extractionCode k).length*
        ((1001*(n+1)*(L+1)*offsetGrowth)*(extractionPrecision k p+1)^64+
          (cachePrecisionBudget L (extractionPrecision k p)+1)*(100*(halvingBudget k+3)+4)) := by
  have h := Nat.add_le_add (extractionArithmeticOperations_bound entry inverseLabel table L k p hL)
    (extractionTargetCacheOperations_bound L k p)
  unfold extractionWithTargetOperations
  simpa only [Nat.mul_add] using h

/-- The actual closed provider supplies the linear envelope used by the
numerical integer-expression trace, with coefficients proved from k. -/
theorem extractionCode_provider_BitEnvelope {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) :
    PacketBitEnvelope u.packetExpression (1000000*(k+3)^7,5000000*(k+3)^7) := by
  intro p
  have h := (u.packetExpression_budget (extractionCode_fits k (.single i u) hu).1 p).trans
    (providerHeightBudget_polynomial k p)
  calc
    _ ≤ 1000000*(k+3)^7*(p+5) := h
    _ = _ := by simp only [Prod.fst,Prod.snd];ring

theorem packetLiteral_budget_of_height (a : IntegerPacket) (B : ℕ) (h : IntegerPacketHeight a B) :
    (PacketExpression.literal a.value).integerBitBudget≤4*(B+1) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin 4) _ =>
    rationalBinaryExponent_le (a.coordinate i) B (IntegerPacket.coordinate_height a B h i))
  simpa only [PacketExpression.integerBitBudget,IntegerPacket.coordinate_value,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hs

/-- The cached literal oracle admits a flat integer budget, including the
out-of-cache default packet, without any opaque target-provider premise. -/
theorem extractionCode_cachedTarget_BitEnvelope {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (P : ℕ) :
    PacketBitEnvelope (fun r => .literal (readPacketCache (buildPacketCache u.quaternionOracle P).1 r))
      (0,4*(1000000*(k+3)^7*(P+5)+1)) := by
  intro r
  change (PacketExpression.literal (readPacketCache (buildPacketCache u.quaternionOracle P).1 r)).integerBitBudget≤_
  by_cases hr : r≤P
  · have hv := buildPacketCache_agrees u.quaternionOracle P r hr
    rw [hv,← u.integerPacket_value r]
    have hb : IntegerPacketHeight (u.integerPacket r) (1000000*(k+3)^7*(P+5)) :=
      IntegerPacketHeight.mono _ _ _ (extractionCode_provider_integerHeight hu r)
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hr 5))
    simpa only [Prod.fst,Prod.snd,zero_mul,zero_add] using packetLiteral_budget_of_height _ _ hb
  · simp [readPacketCache,hr,PacketExpression.integerBitBudget,quaternionOracleOne,
      Fin.sum_univ_four,rationalBinaryExponent]
    norm_num

theorem extractionCode_actualCachedTarget_BitEnvelope {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    PacketBitEnvelope (fun r => .literal (readPacketCache
      (buildPacketCache u.quaternionOracle (numericalDemand L (Nat.clog 2 (q+1)))).1 r))
        (0,4*(1000000*(k+3)^7*(cachePrecisionBudget L q+5)+1)) := by
  intro r
  have h := extractionCode_cachedTarget_BitEnvelope hu (numericalDemand L (Nat.clog 2 (q+1))) r
  have hp := numericalDemand_precision_bound L q
  simp only [Prod.fst,Prod.snd,zero_mul,zero_add] at h ⊢
  exact h.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 5)) 1))

end EffectiveEncoding
