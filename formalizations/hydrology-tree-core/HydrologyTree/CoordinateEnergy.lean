import HydrologyTree.PathNormalization

/-! Unscaled coordinate transport: a direct finite bilinear-form proof that
all path coefficient and physical-array reorderings preserve coefficient dot
products. This closes the possible hidden size-dependent scaling of Jacobians. -/
open Polynomial Module Matrix
noncomputable section
namespace HydrologyTree

def coefficientDot (n : ℕ) (p q : Coeff n) : ℝ :=
  ∑ i : Fin n, (p : ℝ[X]).coeff i * (q : ℝ[X]).coeff i

def pathCoefficientDot (n : ℕ) (p q : PathCoefficients n) : ℝ :=
  coefficientDot (n+1) p.1 q.1 + coefficientDot n p.2 q.2

def physicalRateDot (n : ℕ) (x y : TreeRates n) : ℝ :=
  (∑ i : Fin (n+1), x.1 i * y.1 i) + ∑ i : Fin n, x.2 i * y.2 i

@[reducible] def nestedPathDot : (n : ℕ) → PathRates n → PathRates n → ℝ
  | 0, x, y => x*y
  | n+1, x, y => nestedPathDot n x.1 y.1 + x.2.1*y.2.1 + x.2.2*y.2.2

lemma coefficientDot_succ (n : ℕ) (p q : Coeff (n+1)) :
    coefficientDot (n+1) p q = (p : ℝ[X]).coeff n * (q : ℝ[X]).coeff n +
      coefficientDot n (cut n (p : ℝ[X])) (cut n (q : ℝ[X])) := by
  simp only [coefficientDot, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.val_last, cut_coeff]
  exact add_comm _ _

lemma coefficientDot_two (n : ℕ) (p q : Coeff (n+2)) :
    coefficientDot (n+2) p q =
      (p : ℝ[X]).coeff (n+1) * (q : ℝ[X]).coeff (n+1) +
      (p : ℝ[X]).coeff n * (q : ℝ[X]).coeff n +
      coefficientDot n (cut n (p : ℝ[X])) (cut n (q : ℝ[X])) := by
  rw [coefficientDot_succ (n+1), coefficientDot_succ n,
    cut_coeff (n+1) (p : ℝ[X]) ⟨n, Nat.lt_succ_self n⟩,
    cut_coeff (n+1) (q : ℝ[X]) ⟨n, Nat.lt_succ_self n⟩,
    cut_cut (Nat.le_succ n), cut_cut (Nat.le_succ n)]
  ring

lemma prependRateEquiv_dot (n : ℕ) (x y : TreeRates n) (a b c d : ℝ) :
    physicalRateDot (n+1) (prependRateEquiv n (x,(a,b)))
      (prependRateEquiv n (y,(c,d))) = physicalRateDot n x y + a*c + b*d := by
  simp only [physicalRateDot, prependRateEquiv_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring

/-- The recursive rate equivalence is unscaled in the original physical arrays. -/
theorem pathRateEquiv_dot (n : ℕ) (x y : PathRates n) :
    physicalRateDot n (pathRateEquiv n x) (pathRateEquiv n y) = nestedPathDot n x y := by
  induction n with
  | zero => simp [pathRateEquiv, singletonRateEquiv, physicalRateDot, nestedPathDot]
  | succ n ih =>
    rw [pathRateEquiv_succ, pathRateEquiv_succ, prependRateEquiv_dot, ih]

lemma pathCoefficientEquiv_explicit_succ (n : ℕ) (p : PathCoefficients (n+1)) :
    pathCoefficientEquiv (n+1) p =
      (pathCoefficientEquiv n (p.2,cut n (p.1 : ℝ[X])),
        ((p.1 : ℝ[X]).coeff (n+1),(p.1 : ℝ[X]).coeff n)) := by
  change (pathCoefficientEquiv n (p.2, (topTwoEquiv n p.1).2),
    (topTwoEquiv n p.1).1) = _
  rw [topTwoEquiv_apply]

/-- The output-coordinate equivalence only reorders existing coefficients. -/
theorem pathCoefficientEquiv_dot (n : ℕ) (p q : PathCoefficients n) :
    nestedPathDot n (pathCoefficientEquiv n p) (pathCoefficientEquiv n q) =
      pathCoefficientDot n p q := by
  induction n with
  | zero =>
    change (p.1 : ℝ[X]).coeff 0 * (q.1 : ℝ[X]).coeff 0 = _
    simp [pathCoefficientDot, coefficientDot, Fin.sum_univ_succ]
  | succ n ih =>
    rw [pathCoefficientEquiv_explicit_succ, pathCoefficientEquiv_explicit_succ]
    change nestedPathDot n (pathCoefficientEquiv n _) (pathCoefficientEquiv n _) + _ + _ = _
    rw [ih]
    unfold pathCoefficientDot
    rw [coefficientDot_two]
    ring

/-- Dot product in an arbitrary finite basis. -/
def basisDot {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (b : Basis I ℝ E) (x y : E) : ℝ := ∑ i, b.repr x i * b.repr y i

/-- A bilinear-form-preserving coefficient map has determinant square one. -/
theorem det_sq_of_basisDot_preserved {E F I : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [Fintype I] [DecidableEq I] (bE : Basis I ℝ E) (bF : Basis I ℝ F)
    (L : E →ₗ[ℝ] F) (hL : ∀ x y, basisDot bF (L x) (L y) = basisDot bE x y) :
    (LinearMap.toMatrix bE bF L).det ^ 2 = 1 := by
  let M := LinearMap.toMatrix bE bF L
  have hM : M.transpose * M = 1 := by
    ext i j
    change (∑ k : I, M k i * M k j) = (1 : Matrix I I ℝ) i j
    simp only [M, LinearMap.toMatrix_apply]
    change basisDot bF (L (bE i)) (L (bE j)) = _
    rw [hL]
    simp [basisDot, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  simpa only [pow_two] using hd

end HydrologyTree
