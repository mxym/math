import QuantumCore

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

namespace ECQC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Born rule for a pure state is the squared modulus of its actual amplitude. -/
theorem born_pureState (psi v : n → ℂ) :
    born (pureState psi) v = Complex.normSq (dotProduct (star v) psi) := by
  have hm : pureState psi *ᵥ v = (dotProduct (star psi) v) • psi := by
    ext i
    simp only [pureState, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [born, hm, dotProduct_smul, Matrix.star_dotProduct psi v]
  change (conj (dotProduct (star v) psi) * dotProduct (star v) psi).re = _
  rw [← Complex.normSq_eq_conj_mul_self]
  rfl

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A joint measurement outcome vector in the standard tensor-product basis. -/
def localOutcome (B : Matrix n n ℂ) (C : Matrix m m ℂ) (j : n) (k : m) : n × m → ℂ :=
  fun x => B x.1 j * C x.2 k

/-- The actual Born probability table for a pair of local measurement bases. -/
def bornTable (A : Matrix (n × m) (n × m) ℂ) (B : Matrix n n ℂ)
    (C : Matrix m m ℂ) : Matrix n m ℝ :=
  fun j k => born A (localOutcome B C j k)

end ECQC
