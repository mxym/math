import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-! Definitions retain the original order of all four matrix indices. -/
namespace QPermanentHalfline

/-- The number of pairs i < j for which σ i > σ j. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

/-- The q-permanent as a sum over every permutation, with its actual inversion number. -/
def qPermanent {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (q : R) : R :=
  letI : Fintype (Equiv.Perm (Fin n)) := fintypePerm
  ∑ σ : Equiv.Perm (Fin n), q ^ inversions σ * ∏ i : Fin n, A i (σ i)

/-- Exact rational matrix from the fixed public counterexample. -/
def rationalMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, -(99/100), 0, 1/500;
     -(99/100), 1, 0, 1/8;
     0, 0, 1, 0;
     1/500, 1/8, 0, 1]

/-- The same rational entries interpreted in the real numbers. -/
def counterexampleMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (rationalMatrix i j : ℝ)

theorem qPermanent_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (q : R) :
    qPermanent (fun i j => f (A i j)) (f q) = f (qPermanent A q) := by
  simp [qPermanent, map_sum, map_mul, map_pow, map_prod]

end QPermanentHalfline
