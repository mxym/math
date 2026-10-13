import HydrologyTree.PathRootTransform

/-! Exact coefficient interpretation of the one-child root transformation.
All coefficient permutations, including degree-zero tails, are explicit. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

abbrev PathCoefficients (n : ℕ) := Coeff (n+1) × Coeff n
abbrev PathPolyData (n : ℕ) := RootTransitionSpace (Coeff (n+1)) (Coeff n)

lemma cut_cut {n m : ℕ} (h : n ≤ m) (p : ℝ[X]) :
    cut n (cut m p : ℝ[X]) = cut n p := by
  apply (degreeLTEquiv ℝ n).injective
  funext i
  change ((cut n (cut m p : ℝ[X]) : Coeff n) : ℝ[X]).coeff i =
    ((cut n p : Coeff n) : ℝ[X]).coeff i
  rw [cut_coeff, cut_coeff]
  exact cut_coeff m p ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- High-first two coefficients and the remaining low coefficients. -/
def topTwoEquiv (n : ℕ) : Coeff (n+2) ≃ₗ[ℝ] ((ℝ × ℝ) × Coeff n) :=
  (leadingEquiv (n+1)).symm |>.trans
    ((LinearEquiv.refl ℝ ℝ).prodCongr (leadingEquiv n).symm) |>.trans
    (LinearEquiv.prodAssoc ℝ ℝ ℝ (Coeff n)).symm

@[simp] lemma topTwoEquiv_apply (n : ℕ) (p : Coeff (n+2)) :
    topTwoEquiv n p =
      (((p : ℝ[X]).coeff (n+1), (p : ℝ[X]).coeff n), cut n (p : ℝ[X])) := by
  change (((p : ℝ[X]).coeff (n+1), ((cut (n+1) (p : ℝ[X]) : ℝ[X])).coeff n),
      cut n (cut (n+1) (p : ℝ[X]) : ℝ[X])) = _
  rw [cut_coeff (n+1) (p : ℝ[X]) ⟨n, Nat.lt_succ_self n⟩, cut_cut (Nat.le_succ n)]

/-- A rate-independent permutation of the actual parent polynomial coefficients. -/
def parentCoefficientEquiv (n : ℕ) : PathCoefficients (n+1) ≃ₗ[ℝ] PathPolyData n :=
  (LinearEquiv.prodComm ℝ (Coeff (n+2)) (Coeff (n+1))).trans
    ((LinearEquiv.refl ℝ (Coeff (n+1))).prodCongr (topTwoEquiv n))

def pathTop (n : ℕ) : Coeff (n+1) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Polynomial.lcoeff ℝ n).comp (degreeLT ℝ (n+1)).subtype)

def pathNext (n : ℕ) : Coeff (n+1) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (((Polynomial.lcoeff ℝ n).comp
    (LinearMap.mulLeft ℝ (X : ℝ[X]))).comp (degreeLT ℝ (n+1)).subtype)

def pathLow (n : ℕ) : Coeff (n+1) →L[ℝ] Coeff n :=
  LinearMap.toContinuousLinearMap ((cut n).comp (degreeLT ℝ (n+1)).subtype)

def pathShift (n : ℕ) : Coeff (n+1) →L[ℝ] Coeff n :=
  LinearMap.toContinuousLinearMap (((cut n).comp (LinearMap.mulLeft ℝ (X : ℝ[X]))).comp
    (degreeLT ℝ (n+1)).subtype)

/-- The actual characteristic polynomial when one child is attached at the root. -/
def pathStepPolynomial {n : ℕ} (z : PathPolyData n) : ℝ[X] :=
  (X + C z.2.1.1) * (monicPoly z.1 : ℝ[X]) - C z.2.1.2 * (monicPoly z.2.2 : ℝ[X])

def pathStepCoefficients {n : ℕ} (z : PathPolyData n) : PathCoefficients (n+1) :=
  (cut (n+2) (pathStepPolynomial z), z.1)

lemma pathStepPolynomial_top {n : ℕ} (z : PathPolyData n) :
    (pathStepPolynomial z).coeff (n+1) = z.2.1.1 + pathTop n z.1 := by
  simp only [pathStepPolynomial, coe_monicPoly, add_mul, mul_add,
    Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rw [show (X : ℝ[X]) * X^(n+1) = X^(n+2) by exact (pow_succ' (X : ℝ[X]) (n+1)).symm]
  rw [Polynomial.coeff_X_mul]
  simp only [Polynomial.coeff_X_pow, coeff_eq_zero_of_bound z.1 le_rfl,
    coeff_eq_zero_of_bound z.2.2 (Nat.le_succ n),
    if_neg (show n+1 ≠ n+2 from by omega), if_neg (show n+1 ≠ n from by omega),
    if_pos rfl, mul_zero, mul_one, zero_add, add_zero, sub_zero]
  simp only [ite_true, mul_one]
  rfl

lemma pathStepPolynomial_next {n : ℕ} (z : PathPolyData n) :
    (pathStepPolynomial z).coeff n = pathNext n z.1 + z.2.1.1 * pathTop n z.1 - z.2.1.2 := by
  simp only [pathStepPolynomial, coe_monicPoly, add_mul, mul_add,
    Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rw [show (X : ℝ[X]) * X^(n+1) = X^(n+2) by exact (pow_succ' (X : ℝ[X]) (n+1)).symm]
  simp only [Polynomial.coeff_X_pow, coeff_eq_zero_of_bound z.2.2 le_rfl,
    if_neg (show n ≠ n+2 from by omega), if_neg (show n ≠ n+1 from by omega),
    if_pos rfl, mul_zero, mul_one, zero_add, add_zero, ite_true]
  rfl

lemma pathStepPolynomial_low {n : ℕ} (z : PathPolyData n) :
    cut n (pathStepPolynomial z) =
      pathShift n z.1 + z.2.1.1 • pathLow n z.1 - z.2.1.2 • z.2.2 := by
  simp only [pathStepPolynomial, coe_monicPoly, add_mul, mul_add, map_sub, map_add]
  rw [show (X : ℝ[X]) * X^(n+1) = X^(n+2) by exact (pow_succ' (X : ℝ[X]) (n+1)).symm]
  simp only [← smul_eq_C_mul, map_smul, cut_X_pow_of_le n (n+2) (by omega),
    cut_X_pow_of_le n (n+1) (by omega), cut_X_pow_of_le n n le_rfl,
    smul_zero, cut_coe, zero_add, add_zero]
  rfl

/-- The explicit triangular endomorphism is exactly the actual coefficient
operation followed by the stated coefficient permutation. -/
theorem parentCoefficient_step_eq {n : ℕ} (z : PathPolyData n) :
    parentCoefficientEquiv n (pathStepCoefficients z) =
      rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n) z := by
  change (z.1, topTwoEquiv n (cut (n+2) (pathStepPolynomial z))) = _
  rw [topTwoEquiv_apply]
  rw [cut_coeff (n+2) (pathStepPolynomial z) ⟨n+1, by omega⟩,
    cut_coeff (n+2) (pathStepPolynomial z) ⟨n, by omega⟩, cut_cut (show n ≤ n+2 by omega)]
  rw [pathStepPolynomial_top, pathStepPolynomial_next, pathStepPolynomial_low]
  rfl

lemma finrank_coeff (n : ℕ) : Module.finrank ℝ (Coeff n) = n := by
  simpa using Module.finrank_eq_card_basis (degreeLT.basis ℝ n)

/-- Actual one-child polynomial coefficient determinant at all real data. -/
theorem pathStep_jacobian (n : ℕ) (z : PathPolyData n) :
    endJacobian (fun w => parentCoefficientEquiv n (pathStepCoefficients w)) z =
      (-1 : ℝ)^(n+1) * z.2.1.2^n := by
  have he : (fun w => parentCoefficientEquiv n (pathStepCoefficients w)) =
      rootTransition (pathTop n) (pathNext n) (pathShift n) (pathLow n) := by
    funext w; exact parentCoefficient_step_eq w
  rw [he, endJacobian_rootTransition, finrank_coeff]

end HydrologyTree
