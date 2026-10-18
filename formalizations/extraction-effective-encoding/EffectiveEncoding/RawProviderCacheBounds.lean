import EffectiveEncoding.RawProviderBudgets

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- All raw target-program root charges at the actual eager cache requests. -/
def rawTargetProgramCacheCharge (u : SingleCode) (L q : ℕ) : ℕ :=
  ∑ r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1),(u.rawPacketProgram r.val).rootCharge

def rawProviderRootBudget (k r : ℕ) : ℕ :=
  (16*(2*(1000000*(k+3)^7*(r+5))+2)+5)*(100*(halvingBudget k+3)+4)


theorem rawProviderRootBudget_mono {k r s : ℕ} (h : r≤s) :
    rawProviderRootBudget k r≤rawProviderRootBudget k s := by
  unfold rawProviderRootBudget
  gcongr


theorem rawTargetProgramCacheCharge_bound {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    rawTargetProgramCacheCharge u L q≤
      (cachePrecisionBudget L q+1)*rawProviderRootBudget k (cachePrecisionBudget L q) := by
  have hr (r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1)) : r.val≤cachePrecisionBudget L q := by
    exact (Nat.le_of_lt_succ r.isLt).trans (numericalDemand_precision_bound L q)
  have hs': rawTargetProgramCacheCharge u L q≤
      (numericalDemand L (Nat.clog 2 (q+1))+1)*rawProviderRootBudget k (cachePrecisionBudget L q) := by
    unfold rawTargetProgramCacheCharge
    calc
      _≤∑ _r : Fin (numericalDemand L (Nat.clog 2 (q+1))+1),rawProviderRootBudget k (cachePrecisionBudget L q) := by
        exact Finset.sum_le_sum (fun r _ => (extractionCode_rawPacketProgram_rootCharge hu r.val).trans
          (rawProviderRootBudget_mono (hr r)))
      _=_ := by simp
  exact hs'.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (numericalDemand_precision_bound L q) 1))

/-- Root-only provider cache coefficient, independent of the requested q. -/
def rawProviderCacheRootCoefficient (k L : ℕ) : ℕ :=
  (51200000*(L+1)+1)*
    (16*(2*(1000000*(k+3)^7*(51200000*(L+1)+5))+2)+5)*(100*(halvingBudget k+3)+4)


theorem rawProviderCacheRoot_algebra (A C F x : ℕ) (hx : 1≤x) :
    (A*x^9+1)*((16*(2*(C*(A*x^9+5))+2)+5)*F)≤
      ((A+1)*(16*(2*(C*(A+5))+2)+5)*F)*x^18 := by
  let y:=x^9
  have hy : 1≤y := Nat.one_le_pow _ _ (by omega)
  have h1 : A*y+1≤(A+1)*y := by nlinarith
  have h5 : A*y+5≤(A+5)*y := by nlinarith
  have hroot : 16*(2*(C*(A*y+5))+2)+5≤(16*(2*(C*(A+5))+2)+5)*y := by nlinarith
  have h:=Nat.mul_le_mul h1 (Nat.mul_le_mul_right F hroot)
  apply h.trans_eq
  dsimp [y]
  rw [show 18=9+9 by decide,pow_add]
  ring


theorem rawTargetProgramCacheCharge_polynomial {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    rawTargetProgramCacheCharge u L q≤rawProviderCacheRootCoefficient k L*(q+1)^18 := by
  apply (rawTargetProgramCacheCharge_bound hu L q).trans
  exact rawProviderCacheRoot_algebra (51200000*(L+1)) (1000000*(k+3)^7)
    (100*(halvingBudget k+3)+4) (q+1) (by omega)

def rawProviderCachePolynomialConstant (L : ℕ) : ℕ :=
  (51200000*(L+1)+1)*(32000000*(51200000*(L+1)+5)+37)*1104


theorem rawProviderCoefficient_algebra (A X F : ℕ) (hX : 1≤X) (hF : F≤1104*X) :
    (A+1)*(16*(2*(1000000*X^7*(A+5))+2)+5)*F≤
      ((A+1)*(32000000*(A+5)+37)*1104)*X^8 := by
  have hp : 1≤X^7 := Nat.one_le_pow _ _ (by omega)
  have hc : 16*(2*(1000000*X^7*(A+5))+2)+5≤(32000000*(A+5)+37)*X^7 := by nlinarith
  have h:=Nat.mul_le_mul (Nat.mul_le_mul_left (A+1) hc) hF
  apply h.trans_eq
  ring


theorem rawProviderCacheRootCoefficient_polynomial (k L : ℕ) :
    rawProviderCacheRootCoefficient k L≤rawProviderCachePolynomialConstant L*(k+3)^8 := by
  have hc : Nat.clog 2 (k+3)≤k+3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hF : 100*(halvingBudget k+3)+4≤1104*(k+3) := by unfold halvingBudget;omega
  exact rawProviderCoefficient_algebra (51200000*(L+1)) (k+3)
    (100*(halvingBudget k+3)+4) (by omega) hF


theorem rawTargetProgramCacheCharge_polynomial_kq {k : ℕ} {i : Fin (originalWireCount k)} {u : SingleCode}
    (hu : GateCode.single i u∈extractionCode k) (L q : ℕ) :
    rawTargetProgramCacheCharge u L q≤rawProviderCachePolynomialConstant L*(k+3)^8*(q+1)^18 :=
  (rawTargetProgramCacheCharge_polynomial hu L q).trans
    (Nat.mul_le_mul_right _ (rawProviderCacheRootCoefficient_polynomial k L))


end EffectiveEncoding
