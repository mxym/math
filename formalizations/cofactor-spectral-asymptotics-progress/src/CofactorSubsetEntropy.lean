import CofactorEntropyProduct
import Mathlib.Data.Finset.Sort

/-! The geometric entropy estimate for every nonempty selected subset, in its actual order. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem geometric_subset_product_bound {K : Type*} [LinearOrder K]
    (b : ℝ) (hb : 1 < b) (d : K → ℝ) (hd : ∀ i, 0 < d i)
    (hsep : ∀ i j, i < j → b*d i ≤ d j) (s : Finset K) (hs : s.Nonempty) :
    (∑ i ∈ s, d i)^(∑ i ∈ s, d i) / (∏ i ∈ s, d i^d i) ≤
      (entropyConstant b)^(∑ i ∈ s, d i) := by
  classical
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hs))
  let e : Fin (n+1) ≃ s := Fin.revPerm.trans (s.orderIsoOfFin hn).toEquiv
  let a : Fin (n+1) → ℝ := fun i => d (e i).val
  have ha : ∀ i, 0 < a i := fun i => hd _
  have has : ∀ i : Fin n, b*a i.succ ≤ a i.castSucc := by
    intro i
    have hi : (e i.succ).val < (e i.castSucc).val :=
      (s.orderIsoOfFin hn).strictMono (Fin.rev_lt_rev.mpr Fin.castSucc_lt_succ)
    exact hsep _ _ hi
  have h := geometric_separation_product_bound n b hb a ha has
  have hsum : (∑ i, a i) = ∑ i ∈ s, d i := by
    calc
      _ = ∑ j : s, d j.val := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_subtype (F := inferInstance) s (fun _ => Iff.rfl) d).symm
  have hprod : (∏ i, a i^a i) = ∏ i ∈ s, d i^d i := by
    calc
      _ = ∏ j : s, d j.val^d j.val := Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = _ := (Finset.prod_subtype (F := inferInstance) s (fun _ => Iff.rfl)
        (fun i => d i^d i)).symm
  rw [hsum,hprod] at h
  exact h

end
end CofactorSpectral
