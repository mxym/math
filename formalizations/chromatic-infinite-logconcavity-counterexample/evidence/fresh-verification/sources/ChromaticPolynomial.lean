import CycleColoring
import Mathlib.Algebra.Polynomial.Roots

namespace ChromaticC17
open SimpleGraph Polynomial

def allOnes (q : ℕ) : Matrix (Fin q) (Fin q) ℤ := Matrix.of 1

theorem allOnes_mul (q : ℕ) : allOnes q * allOnes q = (q : ℤ) • allOnes q := by
  ext i j
  simp [allOnes, Matrix.mul_apply]

noncomputable def transferCoeff (q : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (q - 1) * transferCoeff q n + (-1) ^ n

theorem transferCoeff_identity (q : ℤ) (n : ℕ) :
    q * transferCoeff q n = (q - 1) ^ n - (-1) ^ n := by
  induction n with
  | zero => simp [transferCoeff]
  | succ n ih =>
    simp only [transferCoeff, pow_succ]
    calc
      q * ((q - 1) * transferCoeff q n + (-1) ^ n) =
          (q - 1) * (q * transferCoeff q n) + q * (-1) ^ n := by ring
      _ = (q - 1) ^ n * (q - 1) - (-1) ^ n * (-1) := by rw [ih]; ring

theorem complete_adj_pow (q n : ℕ) :
    (completeGraph (Fin q)).adjMatrix ℤ ^ n =
      transferCoeff q n • allOnes q + (-1 : ℤ) ^ n • (1 : Matrix (Fin q) (Fin q) ℤ) := by
  induction n with
  | zero => simp [transferCoeff]
  | succ n ih =>
    rw [pow_succ, ih, adjMatrix_completeGraph_eq_of_one_sub_one]
    change (transferCoeff q n • allOnes q + (-1 : ℤ) ^ n • 1) * (allOnes q - 1) = _
    simp only [mul_sub, add_mul, Matrix.smul_mul, allOnes_mul, mul_one, one_mul, smul_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      transferCoeff, pow_succ]
    ring

theorem trace_complete_adj_pow (q n : ℕ) :
    Matrix.trace ((completeGraph (Fin q)).adjMatrix ℤ ^ n) =
      ((q : ℤ) - 1) ^ n + ((q : ℤ) - 1) * (-1) ^ n := by
  rw [complete_adj_pow, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
  have hj : Matrix.trace (allOnes q) = (q : ℤ) := by simp [allOnes, Matrix.trace, Matrix.diag]
  rw [hj]
  simp only [Fintype.card_fin, smul_eq_mul]
  calc
    transferCoeff q n * q + (-1 : ℤ) ^ n * q =
        q * transferCoeff q n + q * (-1 : ℤ) ^ n := by ring
    _ = ((q : ℤ) - 1) ^ n + ((q : ℤ) - 1) * (-1) ^ n := by
      rw [transferCoeff_identity]
      ring

/-- The all-natural-q counting specification, using genuine proper graph colorings. -/
def IsChromaticPolynomial {V : Type*} [Fintype V] (G : SimpleGraph V) (P : ℤ[X]) : Prop :=
  ∀ q : ℕ, P.eval (q : ℤ) = (Fintype.card (G.Coloring (Fin q)) : ℤ)

/-- The all-q counting specification determines the polynomial uniquely. -/
theorem IsChromaticPolynomial.unique {V : Type*} [Fintype V] {G : SimpleGraph V}
    {P Q : ℤ[X]} (hP : IsChromaticPolynomial G P) (hQ : IsChromaticPolynomial G Q) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
  rintro x ⟨q, rfl⟩
  exact (hP q).trans (hQ q).symm

noncomputable def cyclePolynomial : ℤ[X] := (X - 1) ^ 17 - (X - 1)

/-- The candidate polynomial counts the actual cycle graph's proper colorings for every q. -/
theorem cyclePolynomial_isChromatic : IsChromaticPolynomial C17 cyclePolynomial := by
  intro q
  rw [coloring_card_eq_trace, trace_complete_adj_pow]
  norm_num [cyclePolynomial]
  ring

end ChromaticC17
