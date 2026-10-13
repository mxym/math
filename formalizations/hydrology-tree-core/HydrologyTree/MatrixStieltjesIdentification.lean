import HydrologyTree.DiagonalGauge
import HydrologyTree.PositiveResponseFiber

/-! Full-degree Stieltjes identification for arbitrary real matrices. Neither
tree support, stability, signs nor conservation are imposed on the competitor. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma full_stieltjes_pair_coprime {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    IsCoprime (stieltjesDenominator r) (stieltjesNumerator r w) := by
  obtain ⟨x,hx,hP,hF⟩ := positive_tree_stieltjes_realization_exists (pathTree n) r w hr hpos hw hm
  have hJ := positive_stieltjes_fiber_regular (pathTree n) r w hr hpos hw hm ⟨x,hx,hP,hF⟩
  rw [← hP,← hF]
  exact (physicalPair_coprime_iff_all_rates (pathTree n) x).mpr
    ⟨fun e => ne_of_gt (hx.2 e),hJ⟩

/-- Equality of the actual observed inverse entry on the genuine common nonpole
domain determines the complete actual monic characteristic/cofactor pair. -/
theorem matrix_stieltjes_response_iff_pair {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (A : Matrix V V ℝ) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    (∀ s : ℝ,A.charpoly.eval s ≠ 0 → (∀ i,s+r i ≠ 0) →
      (Matrix.scalar V s-A)⁻¹ o o=∑ i,w i/(s+r i)) ↔
      A.charpoly=stieltjesDenominator r ∧ diagonalCofactor A o=stieltjesNumerator r w := by
  constructor
  · intro h
    have hc : stieltjesNumerator r w*A.charpoly=diagonalCofactor A o*stieltjesDenominator r := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (infinite_nonroots (stieltjesDenominator r*A.charpoly)
        (mul_ne_zero (stieltjesDenominator_monic r).ne_zero (Matrix.charpoly_monic A).ne_zero)).mono
      intro s hs
      have heval : (stieltjesDenominator r).eval s*A.charpoly.eval s ≠ 0 := by
        simpa only [Set.mem_setOf_eq,Polynomial.eval_mul] using hs
      have hp := left_ne_zero_of_mul heval
      have hq := right_ne_zero_of_mul heval
      have hi : ∀ i,s+r i ≠ 0 := by
        rw [eval_stieltjesDenominator,Finset.prod_ne_zero_iff] at hp
        exact fun i => hp i (Finset.mem_univ i)
      have he := h s hq hi
      rw [inverse_diagonal_eq_cofactor] at he
      have he' := (stieltjes_quotient_eq_sum r w s hi).trans he.symm
      have hmul := (div_eq_div_iff hp hq).mp he'
      simpa only [Set.mem_setOf_eq,Polynomial.eval_mul] using hmul
    have hd : A.charpoly.natDegree=(stieltjesDenominator r).natDegree := by
      rw [Matrix.charpoly_natDegree_eq_dim,stieltjesDenominator_natDegree,hN]
    have he := full_degree_fraction_unique _ _ _ _ (stieltjesDenominator_monic r)
      (Matrix.charpoly_monic A) hd (full_stieltjes_pair_coprime r w hr hpos hw hm) hc
    exact ⟨he.1.symm,he.2.symm⟩
  · rintro ⟨hP,hF⟩ s _ hs
    rw [inverse_diagonal_eq_cofactor,hP,hF]
    exact stieltjes_quotient_eq_sum r w s hs

end HydrologyTree
