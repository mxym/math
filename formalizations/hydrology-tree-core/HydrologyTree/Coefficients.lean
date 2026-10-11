import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual bounded polynomials, endowed with their coefficient norm.
No polynomial, derivative or determinant identity is assumed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev Coeff (n : ℕ) := Polynomial.degreeLT ℝ n

instance coeffNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (Coeff n) :=
  NormedAddCommGroup.induced _ (Fin n → ℝ) (degreeLTEquiv ℝ n)
    (degreeLTEquiv ℝ n).injective

instance coeffNormedSpace (n : ℕ) : NormedSpace ℝ (Coeff n) :=
  NormedSpace.induced ℝ _ (Fin n → ℝ) (degreeLTEquiv ℝ n)

/-- Retain exactly the coefficients of orders less than `n`. -/
def cut (n : ℕ) : ℝ[X] →ₗ[ℝ] Coeff n :=
  (degreeLTEquiv ℝ n).symm.toLinearMap.comp
    (LinearMap.pi fun i : Fin n => Polynomial.lcoeff ℝ i)

@[simp] theorem degreeLTEquiv_coeff {n : ℕ} (p : Coeff n) (i : Fin n) :
    degreeLTEquiv ℝ n p i = (p : ℝ[X]).coeff i := rfl

@[simp] theorem cut_coeff (n : ℕ) (p : ℝ[X]) (i : Fin n) :
    ((cut n p : Coeff n) : ℝ[X]).coeff i = p.coeff i := by
  exact congrFun ((degreeLTEquiv ℝ n).apply_symm_apply (fun j : Fin n => p.coeff j)) i

@[simp] theorem cut_coe {n : ℕ} (p : Coeff n) : cut n (p : ℝ[X]) = p := by
  apply (degreeLTEquiv ℝ n).injective
  funext i
  simp

/-- Coefficient truncation of the actual polynomial product, as a bilinear map. -/
def mulLM (m n r : ℕ) : Coeff m →ₗ[ℝ] Coeff n →ₗ[ℝ] Coeff r :=
  LinearMap.mk₂ ℝ (fun p q => cut r ((p : ℝ[X]) * (q : ℝ[X])))
    (by intros; simp [add_mul])
    (by intros; simp [smul_mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp [mul_smul_comm])

def mulCLM (m n r : ℕ) : Coeff m →L[ℝ] Coeff n →L[ℝ] Coeff r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Coeff n →ₗ[ℝ] Coeff r) ≃ₗ[ℝ] (Coeff n →L[ℝ] Coeff r)).toLinearMap.comp
      (mulLM m n r))

@[simp] theorem mulCLM_apply {m n r : ℕ} (p : Coeff m) (q : Coeff n) :
    mulCLM m n r p q = cut r ((p : ℝ[X]) * (q : ℝ[X])) := rfl

/-- The linear inclusion of a polynomial of degree `< n` into degree `< n+1`. -/
def liftLM (n : ℕ) : Coeff n →ₗ[ℝ] Coeff (n+1) :=
  (cut (n+1)).comp (degreeLT ℝ n).subtype

def liftCLM (n : ℕ) : Coeff n →L[ℝ] Coeff (n+1) :=
  LinearMap.toContinuousLinearMap (liftLM n)

lemma coeff_eq_zero_of_bound {n : ℕ} (p : Coeff n) {k : ℕ} (hk : n ≤ k) :
    (p : ℝ[X]).coeff k = 0 := by
  exact Polynomial.coeff_eq_zero_of_degree_lt
    ((Polynomial.mem_degreeLT.mp p.property).trans_le (by exact_mod_cast hk))

@[simp] theorem coe_lift {n : ℕ} (p : Coeff n) :
    (liftCLM n p : ℝ[X]) = p := by
  ext k
  by_cases hk : k < n+1
  · exact cut_coeff (n+1) (p : ℝ[X]) ⟨k,hk⟩
  · rw [coeff_eq_zero_of_bound _ (Nat.le_of_not_gt hk),
      coeff_eq_zero_of_bound p (by omega)]

def topMonomial (n : ℕ) : Coeff (n+1) :=
  ⟨X^n, Polynomial.mem_degreeLT.mpr (by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_self n)⟩

def monicPoly {n : ℕ} (p : Coeff n) : Coeff (n+1) :=
  topMonomial n + liftCLM n p

@[simp] theorem coe_monicPoly {n : ℕ} (p : Coeff n) :
    (monicPoly p : ℝ[X]) = X^n + (p : ℝ[X]) := by
  simp [monicPoly, topMonomial]

lemma bounded_natDegree {n : ℕ} (p : Coeff (n+1)) :
    (p : ℝ[X]).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact coeff_eq_zero_of_bound p (by omega)

/-- The affine monic-coordinate map has the actual Frechet derivative equal
    to its coefficient inclusion, including the degree-zero case. -/
theorem hasFDerivAt_monicPoly {n : ℕ} (p : Coeff n) :
    HasFDerivAt monicPoly (liftCLM n) p := by
  exact (liftCLM n).hasFDerivAt.const_add (topMonomial n)

end HydrologyTree
