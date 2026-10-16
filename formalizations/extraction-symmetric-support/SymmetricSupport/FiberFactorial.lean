import SymmetricSupport.PureSpan
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial

open scoped BigOperators

namespace SymmetricSupport

noncomputable section

theorem occupationExponent_sum {D k : ℕ} (s : Sym (Fin D) k) :
    (occupationExponent s).sum (fun _ m => m) = k := by
  exact (Multiset.toFinsupp_sum_eq s.val).trans s.property

theorem product_X_occupation (D k : ℕ) (w : Word D k) :
    (∏ i, MvPolynomial.X (w i) : MvPolynomial (Fin D) ℂ) =
      MvPolynomial.monomial (occupationExponent (occupation D k w)) 1 := by
  apply MvPolynomial.funext
  intro z
  simp only [map_prod, MvPolynomial.eval_X]
  rw [occupationExponent, eval_monomial_multiset]
  change _ = (((List.Vector.ofFn w).toList : List (Fin D)).map z).prod
  simp [List.Vector.toList_ofFn, List.prod_ofFn]

/-- Derives the multinomial size of every occupation fiber from actual word expansion.
No cardinality of the fiber is supplied by the caller. -/
theorem fiberCard_occupation_eq_multinomial (D k : ℕ) (s : Sym (Fin D) k) :
    fiberCard (occupation D k) s = (occupationExponent s).multinomial := by
  classical
  have hp : ((∑ d : Fin D, MvPolynomial.X d : MvPolynomial (Fin D) ℂ) ^ k) =
      ∑ w : Word D k,
        MvPolynomial.monomial (occupationExponent (occupation D k w)) 1 := by
    rw [Fintype.sum_pow]
    exact Finset.sum_congr rfl (fun w _ => product_X_occupation D k w)
  have hc := congrArg (fun p : MvPolynomial (Fin D) ℂ => p.coeff (occupationExponent s)) hp
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, occupationExponent_sum,
    ite_eq_left rfl, MvPolynomial.coeff_sum] at hc
  have heq : ∀ w : Word D k,
      occupationExponent (occupation D k w) = occupationExponent s ↔ occupation D k w = s := by
    intro w
    exact (occupationExponent_injective D k).eq_iff
  simp only [MvPolynomial.coeff_monomial, heq] at hc
  have hn : (∑ w : Word D k, if occupation D k w = s then (1 : ℂ) else 0) =
      (fiberCard (occupation D k) s : ℂ) := by
    rw [← Finset.sum_filter]
    simp [fiberCard]
  rw [hn] at hc
  exact_mod_cast hc.symm

theorem fiberCard_mul_occupation_factorials (D k : ℕ) (s : Sym (Fin D) k) :
    fiberCard (occupation D k) s * (∏ d : Fin D, ((occupationExponent s) d).factorial) =
      k.factorial := by
  classical
  rw [fiberCard_occupation_eq_multinomial,
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), mul_comm]
  rw [Nat.multinomial_spec]
  congr 1
  rw [← Finsupp.sum_fintype (occupationExponent s) (fun _ m => m) (by simp)]
  exact occupationExponent_sum s

end
end SymmetricSupport
