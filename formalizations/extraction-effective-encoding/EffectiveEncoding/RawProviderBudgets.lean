import EffectiveEncoding.RawProviderExpressions

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 1000000

theorem integerFraction_height (N D M : ℕ) (hd : 0<D) (hN : N≤M) (hD : D≤M) :
    IntegerScalarHeight (integerFraction N D hd) (binaryWidth M) := by
  have hp : M≤2^binaryWidth M := (Nat.le_succ M).trans (Nat.le_pow_clog (by decide) (M+1))
  exact ⟨hD.trans hp,by simpa only [integerFraction,Int.natAbs_natCast] using hN.trans hp⟩

theorem AngleAtom.rawExpression_operations (a : AngleAtom) (p : ℕ) :
    (a.rawCosExpression p).operations≤12 ∧ (a.rawSinExpression p).operations≤12 := by
  cases a with
  | pi => constructor <;> exact (by decide : 1≤12)
  | merge A B j =>
    by_cases h : j=0 ∨ A+B=0
    · simp only [rawCosExpression,rawSinExpression,dite_eq_left h,ScalarExpression.operations]
      exact ⟨by decide,by decide⟩
    · simp only [rawCosExpression,rawSinExpression,dite_eq_right h,ScalarExpression.operations,
        rawScalarExpression_operations]
      exact ⟨by decide,by decide⟩

theorem AngleCode.rawExpression_operations (a : AngleCode) (p : ℕ) :
    (a.rawCosExpression p).operations≤12*a.halvings+13 ∧
    (a.rawSinExpression p).operations≤12*a.halvings+13 := by
  have hc := halfCosExpression_operations a.halvings a.atom.rawCosExpression 12
    (fun q => (a.atom.rawExpression_operations q).1) p
  have hs := halfSinExpression_operations a.halvings a.atom.rawCosExpression a.atom.rawSinExpression 12
    (fun q => (a.atom.rawExpression_operations q).1) (fun q => (a.atom.rawExpression_operations q).2) p
  constructor
  · unfold rawCosExpression;omega
  · cases hn : a.negative <;>
      simp only [rawSinExpression,hn,Bool.false_eq_true,ite_false,ite_true,ScalarExpression.operations] <;> omega


theorem SingleCode.rawPacketExpression_operations {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    (u.rawPacketExpression p).operations≤100*(H+3)+4*u.inverseDepth := by
  induction u with
  | hadamard => simp [rawPacketExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth];omega
  | yBasis => simp [rawPacketExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth];omega
  | phase a b =>
    have hca := ((a.half 1).rawExpression_operations (p+3)).1
    have hsa := ((a.half 1).rawExpression_operations (p+3)).2
    have hcb := ((b.half 1).rawExpression_operations (p+3)).1
    have hsb := ((b.half 1).rawExpression_operations (p+3)).2
    have ha := h.1.2
    have hb := h.2.2
    have ha' : (a.half 1).halvings≤H+1 := Nat.add_le_add_right ha 1
    have hb' : (b.half 1).halvings≤H+1 := Nat.add_le_add_right hb 1
    have hc : (rawPhaseCosExpression a b p).operations≤48*H+103 := by
      simp only [rawPhaseCosExpression,ScalarExpression.operations,
        Nat.add_assoc]
      omega
    have hs : (rawPhaseSinExpression a b p).operations≤48*H+104 := by
      simp only [rawPhaseSinExpression,ScalarExpression.operations,
        Nat.add_assoc]
      omega
    simp [rawPacketExpression,PacketExpression.operations,ScalarExpression.operations,Fin.sum_univ_four,inverseDepth]
    omega
  | inverse u ih =>
    have hu := ih h
    simp only [rawPacketExpression,PacketExpression.operations,inverseDepth]
    omega

/-- Rational literal height follows from the actual bounded occupation counts. -/

theorem AngleAtom.rawExpression_budget (a : AngleAtom) (M : ℕ)
    (h : match a with | .pi => True | .merge A B j => A+B≤M ∧ j≤M) (p : ℕ) :
    (a.rawCosExpression p).integerBitBudget≤2*binaryWidth M+4+2*p ∧
    (a.rawSinExpression p).integerBitBudget≤2*binaryWidth M+4+2*p := by
  cases a with
  | pi =>
    norm_num [rawCosExpression,rawSinExpression,ScalarExpression.integerBitBudget,rationalBinaryExponent]
    omega
  | merge A B j =>
    by_cases hz : j=0 ∨ A+B=0
    · simp only [rawCosExpression,rawSinExpression,dite_eq_left hz,ScalarExpression.integerBitBudget]
      norm_num [rationalBinaryExponent]
      omega
    · have hp : 0<A+B := by omega
      have hc:=rawScalarExpression_integerBitBudget (integerFraction A (A+B) hp) (binaryWidth M)
        (integerFraction_height A (A+B) M hp (by omega) h.1)
      have hs:=rawScalarExpression_integerBitBudget (integerFraction B (A+B) hp) (binaryWidth M)
        (integerFraction_height B (A+B) M hp (by omega) h.1)
      simp only [rawCosExpression,rawSinExpression,dite_eq_right hz,ScalarExpression.integerBitBudget]
      constructor <;> omega

theorem AngleCode.rawExpression_budget {M H : ℕ} (a : AngleCode) (h : a.Fits M H) (p : ℕ) :
    (a.rawCosExpression p).integerBitBudget≤halfExpressionBudget (2*binaryWidth M+4) H p ∧
    (a.rawSinExpression p).integerBitBudget≤halfExpressionBudget (2*binaryWidth M+4) H p := by
  have hc := halfCosExpression_budget a.halvings a.atom.rawCosExpression (2*binaryWidth M+4)
    (fun q => (a.atom.rawExpression_budget M h.1 q).1) p
  have hs := halfSinExpression_budget a.halvings a.atom.rawCosExpression a.atom.rawSinExpression (2*binaryWidth M+4)
    (fun q => (a.atom.rawExpression_budget M h.1 q).1) (fun q => (a.atom.rawExpression_budget M h.1 q).2) p
  have hm := halfExpressionBudget_mono (B:=2*binaryWidth M+4) (p:=p) le_rfl h.2 le_rfl
  constructor
  · exact hc.trans hm
  · cases hn : a.negative <;>
      simpa only [rawSinExpression,hn,Bool.false_eq_true,ite_false,ite_true,
        ScalarExpression.integerBitBudget] using hs.trans hm


def rawProviderHeightBudget (M H p : ℕ) : ℕ :=
  8*halfExpressionBudget (2*binaryWidth M+4) (H+1) (p+3)+4

theorem SingleCode.rawPacketExpression_budget {M H : ℕ} (u : SingleCode) (h : u.Fits M H) (p : ℕ) :
    (u.rawPacketExpression p).integerBitBudget≤rawProviderHeightBudget M H p := by
  induction u with
  | hadamard =>
    have hb := halfExpressionBudget_ge (2*binaryWidth M+4) (H+1) (p+3)
    norm_num [rawPacketExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold rawProviderHeightBudget
    omega
  | yBasis =>
    have hb := halfExpressionBudget_ge (2*binaryWidth M+4) (H+1) (p+3)
    norm_num [rawPacketExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold rawProviderHeightBudget
    omega
  | phase a b =>
    have hca := ((a.half 1).rawExpression_budget (h.1.half 1) (p+3)).1
    have hsa := ((a.half 1).rawExpression_budget (h.1.half 1) (p+3)).2
    have hcb := ((b.half 1).rawExpression_budget (h.2.half 1) (p+3)).1
    have hsb := ((b.half 1).rawExpression_budget (h.2.half 1) (p+3)).2
    have hc : (rawPhaseCosExpression a b p).integerBitBudget≤
        4*halfExpressionBudget (2*binaryWidth M+4) (H+1) (p+3)+1 := by
      simp only [rawPhaseCosExpression,ScalarExpression.integerBitBudget,
        Nat.add_assoc]
      omega
    have hs : (rawPhaseSinExpression a b p).integerBitBudget≤
        4*halfExpressionBudget (2*binaryWidth M+4) (H+1) (p+3)+1 := by
      simp only [rawPhaseSinExpression,ScalarExpression.integerBitBudget,
        Nat.add_assoc]
      omega
    norm_num [rawPacketExpression,PacketExpression.integerBitBudget,Fin.sum_univ_four,
      ScalarExpression.integerBitBudget,rationalBinaryExponent]
    unfold rawProviderHeightBudget
    omega
  | inverse u ih => exact ih h

/-- Literal numerator and denominator bounds for the actual integer packet,
without an opaque target provider assumption. -/

theorem rawProviderHeightBudget_le (M H p : ℕ) :
    rawProviderHeightBudget M H p≤2*providerHeightBudget M H p := by
  have hc : 2*binaryWidth M+4+8*(H+1+1)≤2*(binaryWidth M+3+8*(H+1+1)) := by omega
  have h:=Nat.mul_le_mul_right (2^(H+1+1)*(p+3+2)) hc
  unfold rawProviderHeightBudget providerHeightBudget halfExpressionBudget
  nlinarith


theorem extractionCode_rawProviderExpression_budget {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    (u.rawPacketExpression p).integerBitBudget≤2*(1000000*(k+3)^7*(p+5)) :=
  ((u.rawPacketExpression_budget (extractionCode_fits k (.single i u) hu).1 p).trans
    (rawProviderHeightBudget_le (4*k) (halvingBudget k) p)).trans
      (Nat.mul_le_mul_left 2 (providerHeightBudget_polynomial k p))


theorem extractionCode_rawProviderExpression_operations {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    (u.rawPacketExpression p).operations≤100*(halvingBudget k+3)+4 := by
  have h:=extractionCode_fits k (.single i u) hu
  have hs:=u.rawPacketExpression_operations h.1 p
  have hd:=h.2
  omega


theorem extractionCode_rawPacketProgram_rootCharge {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    (u.rawPacketProgram p).rootCharge≤
      (16*(2*(1000000*(k+3)^7*(p+5))+2)+5)*(100*(halvingBudget k+3)+4) :=
  ((PacketExpression.sharedCostedIntegerRun_rootCharge (u.rawPacketExpression p)).trans
    (PacketExpression.binaryRootPrimitiveOperations_bound _ _ (extractionCode_rawProviderExpression_budget hu p))).trans
      (Nat.mul_le_mul_left _ (extractionCode_rawProviderExpression_operations hu p))

/-- Every represented provider subtree, including noncanonical fraction
inputs before the first root, has this internal actual-descriptor bound. -/
theorem extractionCode_rawProviderExpression_subtreeBound {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p : ℕ) :
    (u.rawPacketExpression p).IntegerSubtreeBound (2*(1000000*(k+3)^7*(p+5))) :=
  PacketExpression.integerSubtreeBound _ _ (extractionCode_rawProviderExpression_budget hu p)


theorem rawProviderBinaryExponent (B : ℕ) : 2^(2*(2*B)+2)=2^(4*B+2) := by
  congr 1
  omega

theorem extractionCode_rawProviderExpression_binaryProgramOperandTrace_height {k : ℕ}
    {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (p x : ℕ)
    (hx : x∈(u.rawPacketExpression p).binaryProgramOperandTrace) :
    x≤2^(4*(1000000*(k+3)^7*(p+5))+2) := by
  have h:=PacketExpression.binaryProgramOperandTrace_height _ _
    (extractionCode_rawProviderExpression_budget hu p) x hx
  exact h.trans_eq (rawProviderBinaryExponent _)


end EffectiveEncoding
