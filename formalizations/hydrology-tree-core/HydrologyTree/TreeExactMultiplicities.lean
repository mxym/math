import HydrologyTree.SymbolicTreeJacobian
import HydrologyTree.CoordinateMultiplicity

/-! Exact individual-rate multiplicities in the UNIQUE multivariate polynomial
representing the actual standard-basis characteristic/cofactor Frechet Jacobian.
The missing hidden-coordinate-factor argument is discharged, not assumed. -/
noncomputable section
namespace HydrologyTree

lemma treeProofOrientation_ne_zero {n : ℕ} (t : OrderedTree n) : treeProofOrientation t ≠ 0 := by
  rcases treeProofOrientation_sign t with h | h <;> rw [h] <;> norm_num

/-- Exact algebraic coordinate multiplicity for every finite physical tree. -/
theorem treeJacobian_coordinate_emultiplicity {n : ℕ} (t : OrderedTree n)
    (j : SymbolicRateIndex n) :
    emultiplicity (MvPolynomial.X j) (symbolicJacobian t) = (symbolicRateExponent t j : ℕ∞) := by
  exact coordinateProduct_emultiplicity (symbolicRateExponent t) j
    (symbolicSiblingResidual t) (treeProofOrientation t) (treeProofOrientation_ne_zero t)
    (symbolicSiblingResidual_no_coordinate_factor t j)

/-- Polynomial divisibility formulation with the next exponent rigorously excluded. -/
theorem treeJacobian_coordinate_exact_power {n : ℕ} (t : OrderedTree n) (j : SymbolicRateIndex n) :
    (MvPolynomial.X j)^(symbolicRateExponent t j) ∣ symbolicJacobian t ∧
      ¬(MvPolynomial.X j)^(symbolicRateExponent t j+1) ∣ symbolicJacobian t :=
  emultiplicity_eq_coe.mp (treeJacobian_coordinate_emultiplicity t j)

theorem treeJacobian_coordinate_multiplicity {n : ℕ} (t : OrderedTree n) (j : SymbolicRateIndex n) :
    multiplicity (MvPolynomial.X j) (symbolicJacobian t) = symbolicRateExponent t j :=
  multiplicity_eq_of_emultiplicity_eq_some (treeJacobian_coordinate_emultiplicity t j)

/-- Inward edge multiplicity is EXACTLY the size of its actual rooted subtree. -/
theorem treeJacobian_inward_multiplicity {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inl e.succ)) (symbolicJacobian t) = subtreeVertexCount t e.succ := by
  rw [treeJacobian_coordinate_multiplicity,symbolicRateExponent,if_neg (Fin.succ_ne_zero e)]

/-- Outward edge multiplicity is EXACTLY one less than that subtree size.
In particular outward leaf rates have multiplicity zero. -/
theorem treeJacobian_outward_multiplicity {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    multiplicity (MvPolynomial.X (.inr e)) (symbolicJacobian t) = subtreeVertexCount t e.succ-1 :=
  treeJacobian_coordinate_multiplicity t (.inr e)

/-- The root leak is not an algebraic factor of the Jacobian polynomial. -/
theorem treeJacobian_rootLeak_not_dvd {n : ℕ} (t : OrderedTree n) :
    ¬MvPolynomial.X (.inl (0 : Fin (n+1))) ∣ symbolicJacobian t := by
  have h := treeJacobian_coordinate_exact_power t (.inl 0)
  simpa only [symbolicRateExponent,ite_true,zero_add,pow_one] using h.2

/-- Representation-independent theorem: ANY polynomial representing the actual
Frechet Jacobian has exactly these coordinate multiplicities. -/
theorem actualJacobian_polynomial_exact_multiplicities {n : ℕ} (t : OrderedTree n)
    (q : RatePolynomial n)
    (hq : ∀ x : TreeRates n, MvPolynomial.eval (rateEvaluation x) q = treeCanonicalJacobian t x) :
    ∀ j : SymbolicRateIndex n,
      (MvPolynomial.X j)^(symbolicRateExponent t j) ∣ q ∧
        ¬(MvPolynomial.X j)^(symbolicRateExponent t j+1) ∣ q := by
  rw [symbolicJacobian_unique t q hq]
  exact treeJacobian_coordinate_exact_power t

/-- Constructive existence of the polynomial and proof of all exact powers.
This theorem has NO polynomial-representation or multiplicity premise. -/
theorem exists_actualJacobian_polynomial_with_exact_multiplicities {n : ℕ} (t : OrderedTree n) :
    ∃ q : RatePolynomial n,
      (∀ x : TreeRates n, MvPolynomial.eval (rateEvaluation x) q = treeCanonicalJacobian t x) ∧
      (∀ j : SymbolicRateIndex n,
        (MvPolynomial.X j)^(symbolicRateExponent t j) ∣ q ∧
          ¬(MvPolynomial.X j)^(symbolicRateExponent t j+1) ∣ q) :=
  ⟨symbolicJacobian t,symbolicJacobian_evaluate t,treeJacobian_coordinate_exact_power t⟩

end HydrologyTree
