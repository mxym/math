import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# The genuine cyclotomic polynomial and the basic-CGF conditions

The finite-product condition below uses Mathlib's cyclotomic polynomials, with
indices at least two. Combined with coefficientwise nonnegativity this is the
basic-CGF condition: no extra scalar or monomial factor is permitted.
The unimodality condition ranges over every natural coefficient index, including
the polynomial's zero tail.
-/

namespace CyclotomicCounterexample

open Polynomial

/-- The counterexample, expressed using actual integer cyclotomic polynomials. -/
noncomputable def F : Polynomial ℤ :=
  (cyclotomic 4 ℤ * cyclotomic 9 ℤ * cyclotomic 25 ℤ * cyclotomic 30 ℤ) ^ 6

/-- Every coefficient, including the zero tail, is nonnegative. -/
def NonnegativeCoeffs (f : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, 0 ≤ f.coeff k

/-- A finite product of cyclotomic polynomials of order at least two. -/
def IsCyclotomicProduct (f : Polynomial ℤ) : Prop :=
  ∃ (s : Finset ℕ) (m : ℕ → ℕ),
    (∀ n ∈ s, 2 ≤ n) ∧ f = ∏ n ∈ s, (cyclotomic n ℤ) ^ m n

/-- A basic cyclotomic generating function over the integers. -/
def IsBasicCGF (f : Polynomial ℤ) : Prop :=
  NonnegativeCoeffs f ∧ IsCyclotomicProduct f

/-- Weak unimodality over all indices, not only a finite computed prefix. -/
def UnimodalCoeffs (f : Polynomial ℤ) : Prop :=
  ∃ peak : ℕ,
    (∀ i j : ℕ, i ≤ j → j ≤ peak → f.coeff i ≤ f.coeff j) ∧
    (∀ i j : ℕ, peak ≤ i → i ≤ j → f.coeff j ≤ f.coeff i)

theorem F_monic : F.Monic := by
  exact ((((cyclotomic.monic 4 ℤ).mul (cyclotomic.monic 9 ℤ)).mul
    (cyclotomic.monic 25 ℤ)).mul (cyclotomic.monic 30 ℤ)).pow 6

theorem F_natDegree : F.natDegree = 216 := by
  have h4 := cyclotomic_ne_zero 4 ℤ
  have h9 := cyclotomic_ne_zero 9 ℤ
  have h25 := cyclotomic_ne_zero 25 ℤ
  have h30 := cyclotomic_ne_zero 30 ℤ
  rw [F, natDegree_pow,
    natDegree_mul (mul_ne_zero (mul_ne_zero h4 h9) h25) h30,
    natDegree_mul (mul_ne_zero h4 h9) h25,
    natDegree_mul h4 h9]
  simp only [natDegree_cyclotomic]
  decide

theorem F_degree : F.degree = 216 := by
  rw [degree_eq_natDegree F_monic.ne_zero, F_natDegree]
  rfl

theorem F_ne_one : F ≠ 1 := by
  intro h
  have := F_natDegree
  rw [h] at this
  norm_num at this

theorem F_coeff_zero : F.coeff 0 = 1 := by
  norm_num [F, pow_succ, mul_coeff_zero,
    cyclotomic_coeff_zero ℤ (by norm_num : 1 < 4),
    cyclotomic_coeff_zero ℤ (by norm_num : 1 < 9),
    cyclotomic_coeff_zero ℤ (by norm_num : 1 < 25),
    cyclotomic_coeff_zero ℤ (by norm_num : 1 < 30), one_mul, one_pow]

/-- The cyclotomic product condition needs no coefficient-positivity hypothesis. -/
theorem F_isCyclotomicProduct : IsCyclotomicProduct F := by
  refine ⟨{4, 9, 25, 30}, fun _ => 6, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  · simp [F, Finset.prod_insert, Finset.prod_singleton, mul_pow, mul_assoc]

/-- Integration lemma; the final counterexample discharges this hypothesis. -/
theorem F_isBasicCGF_of_nonnegative (h : NonnegativeCoeffs F) : IsBasicCGF F :=
  ⟨h, F_isCyclotomicProduct⟩

end CyclotomicCounterexample
