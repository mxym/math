import HydrologyTree.PositiveFiberAllocation
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.BigOperators.Fin

/-! Purely algebraic child-factor extraction for arbitrary REAL rate vectors.
No positivity of the competing model is assumed: its monic child factors divide
the prescribed split simple root cofactor and therefore split over the reals. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma monic_split_fin_factorization {k : ℕ} (p : ℝ[X]) (hm : p.Monic)
    (hs : p.Splits) (hd : p.natDegree=k) :
    ∃ q : Fin k → ℝ, p=stieltjesDenominator q := by
  let l := p.roots.toList
  have hl : l.length=k := (Multiset.length_toList p.roots).trans (hs.natDegree_eq_card_roots.symm.trans hd)
  let e : Fin k ≃ Fin l.length := finCongr hl.symm
  let q : Fin k → ℝ := fun i => -l.get (e i)
  refine ⟨q,?_⟩
  have hprod : (l.map (fun z : ℝ => (X-C z : ℝ[X]))).prod =
      (p.roots.map (fun z : ℝ => (X-C z : ℝ[X]))).prod := by
    change ((p.roots.toList.map (fun z : ℝ => (X-C z : ℝ[X]))) : Multiset ℝ[X]).prod = _
    simp
  calc
    p = (l.map (fun z : ℝ => (X-C z : ℝ[X]))).prod :=
      (hs.eq_prod_roots_of_monic hm).trans hprod.symm
    _ = ∏ i : Fin l.length, (X-C (l.get i) : ℝ[X]) := by
      symm
      exact Fin.prod_univ_fun_getElem l (fun z : ℝ => (X-C z : ℝ[X]))
    _ = ∏ i : Fin k, (X-C (l.get (e i)) : ℝ[X]) :=
      (e.prod_comp (fun i => (X-C (l.get i) : ℝ[X]))).symm
    _ = stieltjesDenominator q := by
      simp only [stieltjesDenominator,q,map_neg,sub_eq_add_neg]

/-- Every real-rate model with the specified full simple root cofactor has a
unique actual child-pole allocation. Positivity is deliberately NOT a premise. -/
theorem real_child_allocation_exists {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (b : Fin n → ℝ) (hb : Function.Injective b)
    (hF : physicalRootCofactor t x=stieltjesDenominator b) :
    ∃ a : TreePoleAllocation t, ∀ c,
      childCharacteristic t x c=allocatedDenominator b a c := by
  have hsplit : (stieltjesDenominator b).Splits :=
    Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_add_C (b i))
  have hc (c : RootChild t) : ∃ q : Fin (childEdgeCount t c+1) → ℝ,
      childCharacteristic t x c=stieltjesDenominator q := by
    have hdvd : childCharacteristic t x c ∣ stieltjesDenominator b := by
      rw [← hF,physicalRootCofactor_child_product]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
    exact monic_split_fin_factorization (childCharacteristic t x c)
      (physicalCharacteristic_monic _ _) (hsplit.of_dvd (stieltjesDenominator_monic b).ne_zero hdvd)
      (physicalCharacteristic_natDegree _ _)
  choose q hq using hc
  let r : NumberedChildNodes t → ℝ := fun z => q z.1 z.2
  have heq : stieltjesDenominator r=stieltjesDenominator b := by
    rw [stieltjesDenominator_sigma]
    calc
      (∏ c : RootChild t, stieltjesDenominator (q c)) =
          ∏ c : RootChild t, childCharacteristic t x c :=
        Finset.prod_congr rfl (fun c _ => (hq c).symm)
      _ = physicalRootCofactor t x := (physicalRootCofactor_child_product t x).symm
      _ = stieltjesDenominator b := hF
  obtain ⟨e,he⟩ := stieltjes_factor_matching (numberedEdgeEquiv t) r b hb heq
  refine ⟨allocationOfEquiv e,?_⟩
  intro c
  rw [hq c,allocatedDenominator_of_equiv]
  congr 1
  funext i
  exact he ⟨c,i⟩

end HydrologyTree
