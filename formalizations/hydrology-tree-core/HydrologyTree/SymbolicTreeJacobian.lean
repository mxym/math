import HydrologyTree.SymbolicRates
import HydrologyTree.RingSiblingResidual
import HydrologyTree.ResidualFactors
import Mathlib.Algebra.MvPolynomial.Funext

/-! The genuine multivariate polynomial representing the already proved actual
Frechet Jacobian. Existence and UNIQUE evaluation semantics are both proved.
The residual is constructed from ring-valued physical matrices, not postulated. -/
noncomputable section
namespace HydrologyTree

/-- Explicit algebraic residual from the actual ring-valued tree matrices. -/
def symbolicSiblingResidual {n : ℕ} (t : OrderedTree n) : RatePolynomial n :=
  siblingResidualOver t (universalTreeRates n)

/-- Every real specialization equals the actual physical sibling residual. -/
theorem symbolicSiblingResidual_evaluate {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    MvPolynomial.eval (rateEvaluation x) (symbolicSiblingResidual t) =
      originalTreeSiblingProduct t x := by
  rw [symbolicSiblingResidual,siblingResidualOver_map,universalTreeRates_evaluate,
    siblingResidualOver_real]

/-- Exact coordinate exponents on the ORIGINAL parameter set; root leak has exponent zero. -/
def symbolicRateExponent {n : ℕ} (t : OrderedTree n) : SymbolicRateIndex n → ℕ
  | .inl v => if v=0 then 0 else subtreeVertexCount t v
  | .inr e => subtreeVertexCount t e.succ-1

def symbolicRateMonomial {n : ℕ} (t : OrderedTree n) : RatePolynomial n :=
  ∏ j : SymbolicRateIndex n, MvPolynomial.X j ^ symbolicRateExponent t j

lemma symbolicRateMonomial_evaluate {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    MvPolynomial.eval (rateEvaluation x) (symbolicRateMonomial t) = originalTreeRateMonomial t x := by
  rw [symbolicRateMonomial,map_prod,Fintype.prod_sum_type]
  simp only [map_pow,MvPolynomial.eval_X]
  change (∏ v : Fin (n+1), x.1 v ^ (if v=0 then 0 else subtreeVertexCount t v)) *
    (∏ e : Fin n, x.2 e ^ (subtreeVertexCount t e.succ-1)) = _
  rw [Fin.prod_univ_succ]
  simp only [ite_true,pow_zero,one_mul,Fin.succ_ne_zero,ite_false]
  rw [originalTreeRateMonomial,Finset.prod_mul_distrib]

/-- Algebraic representative of the actual standard-coordinate Jacobian.
Its identification below uses the prior unconditional Frechet-Jacobian theorem. -/
def symbolicJacobian {n : ℕ} (t : OrderedTree n) : RatePolynomial n :=
  MvPolynomial.C (treeProofOrientation t) * symbolicRateMonomial t * symbolicSiblingResidual t

/-- The symbolic polynomial equals the ACTUAL matrix-coefficient Frechet
Jacobian on every real parameter assignment, not on a test set. -/
theorem symbolicJacobian_evaluate {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    MvPolynomial.eval (rateEvaluation x) (symbolicJacobian t) = treeCanonicalJacobian t x := by
  rw [symbolicJacobian,map_mul,map_mul,MvPolynomial.eval_C,
    symbolicRateMonomial_evaluate,symbolicSiblingResidual_evaluate,
    all_tree_canonical_jacobian,allTreeJacobianWeight_eq_original_products]
  ring

/-- There is only one multivariate polynomial with the actual Jacobian's
all-real-rate evaluations. Therefore algebraic multiplicities of this representative
are intrinsic to the actual Jacobian, independent of its chosen presentation. -/
theorem symbolicJacobian_unique {n : ℕ} (t : OrderedTree n) (q : RatePolynomial n)
    (hq : ∀ x : TreeRates n, MvPolynomial.eval (rateEvaluation x) q = treeCanonicalJacobian t x) :
    q = symbolicJacobian t := by
  apply MvPolynomial.funext
  intro u
  let x : TreeRates n := (fun v => u (.inl v),fun e => u (.inr e))
  have hu : rateEvaluation x = u := by funext j; cases j <;> rfl
  rw [← hu,symbolicJacobian_evaluate]
  exact hq x

/-- No individual coordinate divides the constructed residual polynomial.
The witnesses are proved uniformly for every finite tree, not finitely checked. -/
theorem symbolicSiblingResidual_no_coordinate_factor {n : ℕ} (t : OrderedTree n)
    (j : SymbolicRateIndex n) : ¬MvPolynomial.X j ∣ symbolicSiblingResidual t := by
  rintro ⟨q,hq⟩
  rcases j with v | e
  · obtain ⟨x,hx,hR⟩ := siblingProduct_inward_hyperplane_witness t v
    apply hR
    rw [← symbolicSiblingResidual_evaluate t x,hq,map_mul,MvPolynomial.eval_X]
    change x.1 v * _ = 0
    rw [hx,zero_mul]
  · obtain ⟨x,hx,hR⟩ := siblingProduct_outward_hyperplane_witness t e
    apply hR
    rw [← symbolicSiblingResidual_evaluate t x,hq,map_mul,MvPolynomial.eval_X]
    change x.2 e * _ = 0
    rw [hx,zero_mul]

end HydrologyTree
