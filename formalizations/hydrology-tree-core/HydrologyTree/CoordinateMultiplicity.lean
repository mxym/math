import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Multiplicity
import Mathlib.Basic.Real.Basic

/-! Exact algebraic multiplicity of an individual variable in a monomial times
a residual without that variable factor. This is polynomial divisibility, not
numerical order estimation or arbitrary-function factorization. -/
noncomputable section
namespace HydrologyTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateMonomial_emultiplicity (d : ι → ℕ) (j : ι) :
    emultiplicity (MvPolynomial.X j : MvPolynomial ι ℝ)
      (∏ i : ι, MvPolynomial.X i ^ d i) = (d j : ℕ∞) := by
  have hp : Prime (MvPolynomial.X j : MvPolynomial ι ℝ) := MvPolynomial.X_prime
  rw [Finset.emultiplicity_prod hp]
  have hterm (i : ι) :
      emultiplicity (MvPolynomial.X j : MvPolynomial ι ℝ) (MvPolynomial.X i ^ d i) =
        if i=j then (d i : ℕ∞) else 0 := by
    by_cases hij : i=j
    · subst i
      rw [emultiplicity_pow_self_of_prime hp,if_pos rfl]
    · have hn : ¬(MvPolynomial.X j : MvPolynomial ι ℝ) ∣ MvPolynomial.X i := by
        intro h
        exact hij (MvPolynomial.X_dvd_X.mp h).symm
      rw [emultiplicity_pow hp,emultiplicity_eq_zero.mpr hn,mul_zero,if_neg hij]
  simp only [hterm]
  simp

/-- Exact finite multiplicity, with the nonvanishing scalar and residual
nondivisibility made explicit. No conclusion is used as a premise. -/
theorem coordinateProduct_emultiplicity (d : ι → ℕ) (j : ι)
    (q : MvPolynomial ι ℝ) (c : ℝ) (hc : c ≠ 0)
    (hq : ¬MvPolynomial.X j ∣ q) :
    emultiplicity (MvPolynomial.X j)
      (MvPolynomial.C c * (∏ i : ι, MvPolynomial.X i ^ d i) * q) = (d j : ℕ∞) := by
  have hp : Prime (MvPolynomial.X j : MvPolynomial ι ℝ) := MvPolynomial.X_prime
  have hunit : IsUnit (MvPolynomial.C c : MvPolynomial ι ℝ) :=
    (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  rw [emultiplicity_mul hp,emultiplicity_mul hp,
    emultiplicity_of_isUnit_right hp.not_isUnit hunit,
    coordinateMonomial_emultiplicity,emultiplicity_eq_zero.mpr hq,zero_add,add_zero]

/-- Divisibility by exactly the displayed power, not by the next power. -/
theorem coordinateProduct_exact_power (d : ι → ℕ) (j : ι)
    (q : MvPolynomial ι ℝ) (c : ℝ) (hc : c ≠ 0)
    (hq : ¬MvPolynomial.X j ∣ q) :
    (MvPolynomial.X j)^d j ∣ (MvPolynomial.C c * (∏ i : ι, MvPolynomial.X i ^ d i) * q) ∧
      ¬(MvPolynomial.X j)^(d j+1) ∣
        (MvPolynomial.C c * (∏ i : ι, MvPolynomial.X i ^ d i) * q) :=
  emultiplicity_eq_coe.mp (coordinateProduct_emultiplicity d j q c hc hq)

end HydrologyTree
