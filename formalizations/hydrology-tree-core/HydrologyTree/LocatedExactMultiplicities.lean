import HydrologyTree.LocatedAllRateJacobian
import HydrologyTree.LocatedCoordinateMonomial
import HydrologyTree.GraphResidualWitness
import HydrologyTree.CoordinateMultiplicity
import HydrologyTree.TreeExactMultiplicities

/-! Complete exact original-coordinate multiplicities of the independently
defined alternate-leak formal Jacobian. The residual's nondivisibility is a
proved uniform boundary theorem, never an assumption of these final results. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact multivariate polynomial factorization with every original directed
rate exponent displayed; the leak coefficient itself has exponent zero. -/
theorem formalLocatedJacobian_coordinate_factorization {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) :
    formalLocatedJacobian p ell = MvPolynomial.C (treeProofOrientation p.tree) *
      graphCoordinateMonomial (locatedCoordinateExponent p q) * symbolicLocatedResidual p ell := by
  apply MvPolynomial.funext
  intro z
  obtain ⟨y,rfl⟩ := (graphRateArrayEquiv G).surjective z
  rw [formalLocatedJacobian_evaluate,map_mul,map_mul,MvPolynomial.eval_C,
    locatedCoordinateMonomial_evaluate,symbolicLocatedResidual_evaluate]
  simpa only [mul_assoc] using locatedGraphJacobian_all_real_factored hG p q y

/-- Exact finite algebraic multiplicities; no genericity or nonzero-rate premise. -/
theorem formalLocatedJacobian_emultiplicity {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (k : GraphCoordinate G) :
    emultiplicity (MvPolynomial.X k) (formalLocatedJacobian p ell) =
      (locatedCoordinateExponent p q k : ℕ∞) := by
  rw [formalLocatedJacobian_coordinate_factorization hG p q]
  exact coordinateProduct_emultiplicity (locatedCoordinateExponent p q) k _ _
    (treeProofOrientation_ne_zero p.tree) (symbolicLocatedResidual_no_coordinate_factor hG p ell k)

theorem formalLocatedJacobian_exact_power {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (k : GraphCoordinate G) :
    (MvPolynomial.X k)^(locatedCoordinateExponent p q k) ∣ formalLocatedJacobian p ell ∧
      ¬(MvPolynomial.X k)^(locatedCoordinateExponent p q k+1) ∣ formalLocatedJacobian p ell :=
  emultiplicity_eq_coe.mp (formalLocatedJacobian_emultiplicity hG p q k)

theorem formalLocatedJacobian_multiplicity {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (k : GraphCoordinate G) :
    multiplicity (MvPolynomial.X k) (formalLocatedJacobian p ell)=locatedCoordinateExponent p q k :=
  multiplicity_eq_of_emultiplicity_eq_some (formalLocatedJacobian_emultiplicity hG p q k)

/-- An observed inward dart has its subtree size minus one, with one additional
factor exactly when this dart also points toward the leak. -/
theorem located_inward_multiplicity {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr (treeDartEquiv p (.inl e)))) (formalLocatedJacobian p ell) =
      subtreeVertexCount p.tree e.succ-1 + leakCoordinateExponent q (.inr (treeDartEquiv p (.inl e))) := by
  rw [formalLocatedJacobian_multiplicity hG p q]
  simp only [locatedCoordinateExponent,observationCoordinateExponent,Equiv.symm_apply_apply,Sum.elim_inl]

/-- The same rule for the opposite dart, including edges whose subtree size is one. -/
theorem located_outward_multiplicity {n : ℕ} (hG : G.IsTree) {o ell : V}
    (p : RootedTreePresentation n G o) (q : RootedTreePresentation n G ell) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr (treeDartEquiv p (.inr e)))) (formalLocatedJacobian p ell) =
      subtreeVertexCount p.tree e.succ-1 + leakCoordinateExponent q (.inr (treeDartEquiv p (.inr e))) := by
  rw [formalLocatedJacobian_multiplicity hG p q]
  simp only [locatedCoordinateExponent,observationCoordinateExponent,Equiv.symm_apply_apply,Sum.elim_inr]

/-- The external leak rate is not an algebraic factor even when the leak site
is distinct from the observation site; zero leak is not silently excluded. -/
theorem located_leak_variable_not_dvd {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) :
    ¬MvPolynomial.X (.inl ()) ∣ formalLocatedJacobian p ell := by
  have h := formalLocatedJacobian_exact_power hG p (leakRootPresentation hG p ell) (.inl ())
  simpa only [locatedCoordinateExponent,observationCoordinateExponent,leakCoordinateExponent,
    zero_add,zero_add,pow_one] using h.2


/-- The alternate-site formula recovers the original inward exponent exactly
when the observation and leak presentations coincide. -/
theorem located_collocated_inward_multiplicity {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr (treeDartEquiv p (.inl e)))) (formalLocatedJacobian p o) =
      subtreeVertexCount p.tree e.succ := by
  rw [located_inward_multiplicity hG p p e]
  simp only [leakCoordinateExponent,Equiv.symm_apply_apply,Sum.elim_inl]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (subtreeVertexCount_pos p.tree e.succ))

theorem located_collocated_outward_multiplicity {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr (treeDartEquiv p (.inr e)))) (formalLocatedJacobian p o) =
      subtreeVertexCount p.tree e.succ-1 := by
  rw [located_outward_multiplicity hG p p e]
  simp only [leakCoordinateExponent,Equiv.symm_apply_apply,Sum.elim_inr,add_zero]

end HydrologyTree
