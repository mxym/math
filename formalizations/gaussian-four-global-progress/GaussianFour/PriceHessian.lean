import GaussianFour.PriceFrechetTransport

/-! A genuine second Frechet derivative of the original Gaussian price
objective, with its positive matrix and exact constant-shift nullspace. -/
open MeasureTheory ProbabilityTheory Set Filter Module Matrix
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

/-- The actual price Hessian, with no differentiability or Gaussian-flux
hypothesis left as an external assumption. -/
theorem actual_simplicial_price_hessian
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j)) ∧
      (facetLaplacian w).PosSemidef ∧
      HasFDerivAt (fun c => fderiv ℝ (priceObjective v p) c)
        ((priceCovectorMap (d+2)).comp (priceMatrixMap (facetLaplacian w))) b ∧
      ∀ q : Fin (d+2) → ℝ,
        q ⬝ᵥ (facetLaplacian w *ᵥ q) = 0 ↔ ∀ i j, q i = q j := by
  obtain ⟨w,hwd,hwp,hws,hf,hpsd,hd⟩ := actual_simplicial_price_second_variation v p b hv
  have hg := priceGradient_hasFDerivAt_flux v p b hv w (fun q => (hd q).1)
  have hh : HasFDerivAt
      (fun c => priceCovectorMap (d+2) (priceGradient v p c))
      ((priceCovectorMap (d+2)).comp (priceMatrixMap (facetLaplacian w))) b :=
    (priceCovectorMap (d+2)).hasFDerivAt.comp b hg
  have he : (fun c => fderiv ℝ (priceObjective v p) c) =
      (fun c => priceCovectorMap (d+2) (priceGradient v p c)) := by
    funext c
    exact (priceObjective_hasFDerivAt_mass_gradient v p c hv.injective).fderiv
  refine ⟨w,hwd,hwp,hws,hf,hpsd,?_,fun q => (hd q).2.2⟩
  rwa [he]

end GaussianFour
