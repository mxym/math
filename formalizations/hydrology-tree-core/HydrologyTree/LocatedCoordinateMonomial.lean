import HydrologyTree.MatrixEdgeMonomial
import HydrologyTree.LocatedPolynomialWeight

/-! Exact exponents on original graph coordinates: observed subtree size minus
one in both directions, plus one on every edge directed toward the leak. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def observationCoordinateExponent {n : ℕ} {o : V} (p : RootedTreePresentation n G o) : GraphCoordinate G → ℕ
  | .inl _ => 0
  | .inr d => Sum.elim (fun e : Fin n => subtreeVertexCount p.tree e.succ-1)
      (fun e : Fin n => subtreeVertexCount p.tree e.succ-1) ((treeDartEquiv p).symm d)

def leakCoordinateExponent {n : ℕ} {ell : V} (q : RootedTreePresentation n G ell) : GraphCoordinate G → ℕ
  | .inl _ => 0
  | .inr d => Sum.elim (fun _ : Fin n => 1) (fun _ : Fin n => 0) ((treeDartEquiv q).symm d)

def locatedCoordinateExponent {n : ℕ} {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (k : GraphCoordinate G) : ℕ :=
  observationCoordinateExponent p k+leakCoordinateExponent q k

def graphCoordinateMonomial (d : GraphCoordinate G → ℕ) : GraphRatePolynomial G :=
  ∏ k : GraphCoordinate G, MvPolynomial.X k ^ d k

lemma graphCoordinateMonomial_evaluate (d : GraphCoordinate G → ℕ) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (graphCoordinateMonomial d) =
      ∏ k : GraphCoordinate G, graphRateArrayEquiv G y k ^ d k := by
  simp only [graphCoordinateMonomial,map_prod,map_pow,MvPolynomial.eval_X]

lemma leakCoordinateMonomial_evaluate {n : ℕ} {ell : V}
    (q : RootedTreePresentation n G ell) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (graphCoordinateMonomial (leakCoordinateExponent q)) =
      leakInwardProduct q y := by
  rw [graphCoordinateMonomial_evaluate,Fintype.prod_sum_type]
  simp only [leakCoordinateExponent,pow_zero,Finset.prod_const_one,one_mul,graphRateArray_dart]
  rw [← (treeDartEquiv q).prod_comp]
  simp only [Equiv.symm_apply_apply,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    pow_one,pow_zero,Finset.prod_const_one,mul_one]
  rfl

lemma observationCoordinateMonomial_evaluate {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (graphCoordinateMonomial (observationCoordinateExponent p)) =
      edgePowerMonomial p.tree ((graphRateEquiv p).symm y) := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [LinearEquiv.symm_apply_apply,graphCoordinateMonomial_evaluate,Fintype.prod_sum_type]
  simp only [observationCoordinateExponent,pow_zero,Finset.prod_const_one,one_mul,graphRateArray_dart]
  rw [← (treeDartEquiv p).prod_comp]
  simp only [Equiv.symm_apply_apply,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    graphRateEquiv_inward,graphRateEquiv_outward]
  rw [← Finset.prod_mul_distrib]
  simp only [← mul_pow]
  rfl

lemma graphCoordinateMonomial_add (a b : GraphCoordinate G → ℕ) :
    graphCoordinateMonomial (fun k => a k+b k)=graphCoordinateMonomial a*graphCoordinateMonomial b := by
  simp only [graphCoordinateMonomial,pow_add,Finset.prod_mul_distrib]

lemma locatedCoordinateMonomial_evaluate {n : ℕ} {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (y : GraphRates G) :
    MvPolynomial.eval (graphRateArrayEquiv G y) (graphCoordinateMonomial (locatedCoordinateExponent p q)) =
      leakInwardProduct q y * matrixEdgeWeight p.tree (graphObservedMatrix p ell y) := by
  change MvPolynomial.eval (graphRateArrayEquiv G y)
    (graphCoordinateMonomial (fun k => observationCoordinateExponent p k + leakCoordinateExponent q k)) = _
  rw [graphCoordinateMonomial_add,map_mul,
    observationCoordinateMonomial_evaluate,leakCoordinateMonomial_evaluate,graphObserved_edgeWeight]
  ring

end HydrologyTree
