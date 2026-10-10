import GaussianFacetLaplacian
import GaussianFour.TraceSupport

/-! Exact positivity and nullspace of the weighted Gaussian flux Laplacian. -/
open Matrix
open GaussianMeasureBridge
namespace GaussianFour
variable {k : ℕ} [NeZero k]

lemma facetLaplacian_quadratic_identity (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (x : Fin k → ℝ) :
    2 * (x ⬝ᵥ (facetLaplacian w *ᵥ x)) =
      ∑ i, ∑ j, w i j * (x i-x j)^2 := by
  have he : x ⬝ᵥ (facetLaplacian w *ᵥ x) =
      ∑ i, ∑ j, w i j * x i * (x i-x j) := by
    simp only [dotProduct, facetLaplacian_mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hswap : (∑ i, ∑ j, w i j * x j * (x j-x i)) =
      ∑ i, ∑ j, w i j * x i * (x i-x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hsq : (∑ i, ∑ j, w i j * (x i-x j)^2) =
      (∑ i, ∑ j, w i j * x i * (x i-x j)) +
      (∑ i, ∑ j, w i j * x j * (x j-x i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsq, hswap, ← he]
  ring

lemma facetLaplacian_quadratic_nonneg (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j) (x : Fin k → ℝ) :
    0 ≤ x ⬝ᵥ (facetLaplacian w *ᵥ x) := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ => mul_nonneg (hw i j) (sq_nonneg (x i-x j))))
  rw [← facetLaplacian_quadratic_identity w hs x] at h
  linarith

/-- The matrix inequality is established from its exact quadratic form. -/
theorem facetLaplacian_posSemidef (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j) :
    (facetLaplacian w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (facetLaplacian_symmetric w hs)
  intro x
  simpa only [star_trivial] using facetLaplacian_quadratic_nonneg w hs hw x

/-- With positive off-diagonal weights, the nullspace consists precisely of
constant price shifts. No spectral diagonalization assumption is required. -/
theorem facetLaplacian_quadratic_zero_iff_constant
    (w : Fin k → Fin k → ℝ) (hs : ∀ i j, w i j = w j i)
    (hw : ∀ i j, 0 ≤ w i j) (hp : ∀ i j, i ≠ j → 0 < w i j) (x : Fin k → ℝ) :
    x ⬝ᵥ (facetLaplacian w *ᵥ x) = 0 ↔ ∀ i j, x i = x j := by
  constructor
  · intro hz i j
    by_cases hij : i = j
    · subst j; rfl
    have hsum : (∑ a, ∑ b, w a b * (x a-x b)^2) = 0 := by
      rw [← facetLaplacian_quadratic_identity w hs x, hz, mul_zero]
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (s := Finset.univ) (fun b _ => mul_nonneg (hw a b) (sq_nonneg (x a-x b))))).mp hsum i (Finset.mem_univ _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (hw i b) (sq_nonneg (x i-x b)))).mp hrow j (Finset.mem_univ _)
    have hsq : (x i-x j)^2 = 0 := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hp i j hij))
    nlinarith
  · intro hconst
    have hzero : facetLaplacian w *ᵥ x = 0 := by
      ext i
      rw [facetLaplacian_mulVec]
      apply Finset.sum_eq_zero
      intro j _
      rw [hconst i j, sub_self, mul_zero]
    rw [hzero, dotProduct_zero]

/-- Strict curvature in every nonconstant price direction. -/
theorem facetLaplacian_quadratic_pos_of_nonconstant
    (w : Fin k → Fin k → ℝ) (hs : ∀ i j, w i j = w j i)
    (hw : ∀ i j, 0 ≤ w i j) (hp : ∀ i j, i ≠ j → 0 < w i j)
    (x : Fin k → ℝ) (hx : ∃ i j, x i ≠ x j) :
    0 < x ⬝ᵥ (facetLaplacian w *ᵥ x) := by
  have hne : x ⬝ᵥ (facetLaplacian w *ᵥ x) ≠ 0 := by
    intro he
    obtain ⟨i,j,hij⟩ := hx
    exact hij ((facetLaplacian_quadratic_zero_iff_constant w hs hw hp x).mp he i j)
  exact lt_of_le_of_ne (facetLaplacian_quadratic_nonneg w hs hw x) (Ne.symm hne)

end GaussianFour
