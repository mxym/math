import BapatMarkedInversions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

open scoped BigOperators ComplexOrder
open Polynomial Matrix

set_option autoImplicit false

namespace BapatRankTwo

/-- Original ordered inversion statistic on all permutations. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

/-- The actual q-permanent, with no restriction of its permutation sum. -/
def qPermanent {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (q : R) : R :=
  letI : Fintype (Equiv.Perm (Fin n)) := fintypePerm
  ∑ σ : Equiv.Perm (Fin n), q ^ inversions σ * ∏ i, A i (σ i)

/-- Real polynomial encoding the real part of the complex q-permanent on real q. -/
noncomputable def realQPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ[X] :=
  letI : Fintype (Equiv.Perm (Fin n)) := fintypePerm
  ∑ σ : Equiv.Perm (Fin n), C (∏ i, A i (σ i)).re * X ^ inversions σ

theorem realQPolynomial_eval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    (realQPolynomial A).eval q = (qPermanent A (q : ℂ)).re := by
  simp only [realQPolynomial, qPermanent, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X, Complex.re_sum, Complex.mul_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

theorem realQPolynomial_derivative_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (realQPolynomial A).derivative.eval 1 =
      (MarkedInversions.weightedInversionSum A).re := by
  simp [realQPolynomial, eval_finsetSum, derivative_mul, derivative_X_pow,
    MarkedInversions.weightedInversionSum, MarkedInversions.permutationWeight,
    MarkedInversions.originalInversions, inversions, Complex.mul_re, mul_comm]

/-- Gram matrix of the complex two-vectors (a i,b i). -/
def gram {ι : Type*} (a b : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => a i * star (a j) + b i * star (b j)

theorem gram_posSemidef {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    (gram a b).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star a).add
    (Matrix.posSemidef_vecMulVec_self_star b)

theorem gram_isHermitian {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    (gram a b).IsHermitian := (gram_posSemidef a b).isHermitian

/-- The genuine two by two minor of the Gram matrix factors through wedges. -/
theorem gram_minor {ι : Type*} (a b : ι → ℂ) (i j k l : ι) :
    gram a b i k * gram a b j l - gram a b i l * gram a b j k =
      (a i * b j - b i * a j) * star (a k * b l - b k * a l) := by
  simp only [gram, star_sub, star_mul]
  ring

/-- The real diagonal perturbation of a complex matrix. -/
def perturb {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := A + Matrix.diagonal (fun _ => (δ : ℂ))

theorem perturb_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) {δ : ℝ} (hδ : 0 < δ) : (perturb A δ).PosDef := by
  exact Matrix.PosDef.posSemidef_add hA
    (Matrix.PosDef.diagonal fun _ => by exact_mod_cast hδ)

@[simp] theorem perturb_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    perturb A 0 = A := by simp [perturb]

/-- Monotonicity in Bapat's original real interval, on complex Hermitian PD matrices. -/
def BapatConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef →
    MonotoneOn (fun q : ℝ => (qPermanent A (q : ℂ)).re) (Set.Icc (-1) 1)

end BapatRankTwo
