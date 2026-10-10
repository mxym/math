import GaussianFour.PriceMassDifferential
import GaussianFour.LaplacianQuadratic

/-! The actual price objective and its exact positive second variation.
The coefficient matrix is obtained from Gaussian flux, not postulated. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

/-- The priceGradient definition is the derivative of the original integral
objective, for every direction and every prescribed target mass vector. -/
theorem priceObjective_directional_gradient
    (v : Fin k → Space d) (p b q : Fin k → ℝ) (hv : Function.Injective v) :
    HasDerivAt (fun t : ℝ => priceObjective v p (affinePrices b q t))
      (∑ i, q i * priceGradient v p b i) 0 := by
  have hs := expectedScore_directional_derivative v 0 b q hv
  have hl : HasDerivAt (fun t : ℝ => ∑ i, p i * (affinePrices b q t) i)
      (∑ i, p i * q i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [affinePrices, zero_add, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (q i)).const_add (b i)).const_mul (p i)
  have h := hs.add hl
  simp only [affineScores, Pi.zero_apply, smul_zero, add_zero, inner_zero_left,
    Finset.sum_const_zero, zero_sub, winningPartition_mass] at h
  change HasDerivAt (fun t : ℝ => priceObjective v p (affinePrices b q t))
    (-(∑ i, winningMass v b i * q i) + ∑ i, p i * q i) 0 at h
  convert h using 1
  simp only [priceGradient, mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_comm]
  ring

/-- The price-gradient derivative and its quadratic second variation use one
and the same actual positive symmetric Gaussian flux matrix. -/
theorem actual_simplicial_price_second_variation
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j)) ∧
      (facetLaplacian w).PosSemidef ∧
      ∀ q : Fin (d+2) → ℝ,
        HasDerivAt (fun t : ℝ => priceGradient v p (affinePrices b q t))
          (facetLaplacian w *ᵥ q) 0 ∧
        HasDerivAt (fun t : ℝ => ∑ i, q i * priceGradient v p (affinePrices b q t) i)
          (q ⬝ᵥ (facetLaplacian w *ᵥ q)) 0 ∧
        (q ⬝ᵥ (facetLaplacian w *ᵥ q) = 0 ↔ ∀ i j, q i = q j) := by
  obtain ⟨w,hwd,hwp,hws,hf,hd⟩ := actual_simplicial_price_gradient_directional v p b hv
  have hnonneg (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i = j
    · subst j; rw [hwd]; exact le_rfl
    · exact (hwp i j hij).le
  refine ⟨w,hwd,hwp,hws,hf,facetLaplacian_posSemidef w hws hnonneg,?_⟩
  intro q
  refine ⟨hd q,?_,facetLaplacian_quadratic_zero_iff_constant w hws hnonneg hwp q⟩
  change HasDerivAt (fun t : ℝ => ∑ i, q i * priceGradient v p (affinePrices b q t) i)
    (∑ i, q i * (facetLaplacian w *ᵥ q) i) 0
  exact HasDerivAt.fun_sum (fun i _ => (hasDerivAt_pi.mp (hd q) i).const_mul (q i))

end GaussianFour
