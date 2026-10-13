import HydrologyTree.LocatedExactMultiplicities

/-! Complete all-real singular set at every leak location. Zero rate boundaries
are included without division or positivity, and the leak-coordinate exponent
zero is distinguished from residual spectral collisions. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma real_coordinate_power_product_zero_iff {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (d : I → ℕ) :
    (∏ i : I,a i ^ d i)=0 ↔ ∃ i,a i=0 ∧ 0<d i := by
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i,_,hi⟩
    have ha : a i=0 := by
      by_contra h
      exact (pow_ne_zero _ h) hi
    have hd : d i ≠ 0 := by
      intro h
      norm_num [h] at hi
    exact ⟨i,ha,Nat.pos_of_ne_zero hd⟩
  · rintro ⟨i,ha,hd⟩
    exact ⟨i,Finset.mem_univ i,by rw [ha,zero_pow (Nat.ne_of_gt hd)]⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Full boundary criterion for the actual coefficient Jacobian in original
coordinates. Every residual is an actual principal matrix resultant. -/
theorem locatedJacobian_zero_iff_all_rates {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (y : GraphRates G) :
    locatedGraphJacobian p ell y=0 ↔
      (∃ k : GraphCoordinate G,graphRateArrayEquiv G y k=0 ∧ 0<locatedCoordinateExponent p q k) ∨
        matrixSiblingResidual p.tree (graphObservedMatrix p ell y)=0 := by
  rw [← formalLocatedJacobian_evaluate,formalLocatedJacobian_coordinate_factorization hG p q,
    map_mul,map_mul,MvPolynomial.eval_C,graphCoordinateMonomial_evaluate,
    symbolicLocatedResidual_evaluate,mul_eq_zero,mul_eq_zero]
  simp only [treeProofOrientation_ne_zero,false_or,real_coordinate_power_product_zero_iff]

/-- All-zero and signed parameter boundaries are explicitly included in the
finite-graph theorem, with constructed presentations for observation and leak. -/
theorem finite_graph_complete_all_leak_algebra {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1) :
    ∃ p : RootedTreePresentation n G o, ∀ ell : V,
      ∃ q : RootedTreePresentation n G ell,
        formalLocatedJacobian p ell=MvPolynomial.C (treeProofOrientation p.tree) *
          graphCoordinateMonomial (locatedCoordinateExponent p q) * symbolicLocatedResidual p ell ∧
        (∀ k : GraphCoordinate G,
          (MvPolynomial.X k)^locatedCoordinateExponent p q k ∣ formalLocatedJacobian p ell ∧
          ¬(MvPolynomial.X k)^(locatedCoordinateExponent p q k+1) ∣ formalLocatedJacobian p ell) ∧
        (∀ y : GraphRates G,
          MvPolynomial.eval (graphRateArrayEquiv G y) (formalLocatedJacobian p ell)=locatedGraphJacobian p ell y) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  refine ⟨p,fun ell => ?_⟩
  let q := leakRootPresentation hG p ell
  exact ⟨q,formalLocatedJacobian_coordinate_factorization hG p q,
    formalLocatedJacobian_exact_power hG p q,formalLocatedJacobian_evaluate p ell⟩

end HydrologyTree
