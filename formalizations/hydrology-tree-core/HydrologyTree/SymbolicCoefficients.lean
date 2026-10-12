import HydrologyTree.SymbolicRates
import HydrologyTree.CanonicalTree

/-! Coefficient polynomials obtained directly from the symbolic physical matrix.
These are independent of the factorized expression used for the main theorem. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Non-leading coefficients of the actual characteristic and cofactor matrices
with formal independent rate variables. No determinant factorization is used. -/
def symbolicCoefficientPolynomials {n : ℕ} (t : OrderedTree n) :
    SymbolicRateIndex n → RatePolynomial n
  | .inl i => (modelCharacteristicOver t (universalTreeRates n)).coeff i
  | .inr e => ((modelMatrixOver t (universalTreeRates n)).submatrix Fin.succ Fin.succ).charpoly.coeff e

lemma symbolicCofactor_specialize {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (((modelMatrixOver t (universalTreeRates n)).submatrix Fin.succ Fin.succ).charpoly).map
      (MvPolynomial.eval (rateEvaluation x)) = physicalRootCofactor t x := by
  rw [← Matrix.charpoly_map]
  have h := modelMatrixOver_map (MvPolynomial.eval (rateEvaluation x)) t (universalTreeRates n)
  rw [universalTreeRates_evaluate,modelMatrixOver_real] at h
  have hs := congrArg (fun M => M.submatrix Fin.succ Fin.succ) h
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.charpoly) hs

/-- Every formal coefficient specializes to its actual physical coefficient. -/
theorem symbolicCoefficientPolynomials_evaluate {n : ℕ} (t : OrderedTree n)
    (x : TreeRates n) (j : SymbolicRateIndex n) :
    MvPolynomial.eval (rateEvaluation x) (symbolicCoefficientPolynomials t j) =
      rateEvaluation (normalizedPhysicalTree t x) j := by
  rcases j with i | e
  · change MvPolynomial.eval (rateEvaluation x)
      ((modelCharacteristicOver t (universalTreeRates n)).coeff i) = _
    rw [← Polynomial.coeff_map,modelCharacteristicOver_map,universalTreeRates_evaluate,
      modelCharacteristicOver_real]
    exact (cut_coeff (n+1) (physicalCharacteristic t x) i).symm
  · change MvPolynomial.eval (rateEvaluation x)
      (((modelMatrixOver t (universalTreeRates n)).submatrix Fin.succ Fin.succ).charpoly.coeff e) = _
    rw [← Polynomial.coeff_map,symbolicCofactor_specialize]
    exact (cut_coeff n (physicalRootCofactor t x) e).symm

/-- Standard rate-coordinate serialization as a proved linear equivalence. -/
def rateArrayEquiv (n : ℕ) : TreeRates n ≃ₗ[ℝ] (SymbolicRateIndex n → ℝ) :=
  (catenaryArrayInputBasis n).equivFun

lemma rateArrayEquiv_apply {n : ℕ} (x : TreeRates n) : rateArrayEquiv n x = rateEvaluation x := by
  funext j
  rcases j with i | e <;>
    simp [rateArrayEquiv,catenaryArrayInputBasis,Module.Basis.equivFun_apply,rateEvaluation]

end HydrologyTree
