import GaussianSimplicialMassFlux
import GaussianFacetLaplacian

/-! All-cell directional derivatives of actual Gaussian winning masses.
A single flux family works for every price direction and every cell. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

/-- Reindexing moves the proved base-cell slicing derivative to every cell,
without replacing actual Gaussian masses by abstract weights. -/
theorem simplicial_mass_flux_derivative
    (v : Fin (d+2) → Space (d+1)) (b q : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hf : ∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j))
    (i : Fin (d+2)) :
    HasDerivAt (fun t => winningMass v (affinePrices b q t) i)
      (- (facetLaplacian w *ᵥ q) i) 0 := by
  classical
  let e : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
  have he0 : e 0 = i := Equiv.swap_apply_left 0 i
  have hu : AffineIndependent ℝ (v ∘ e) := hv.comp_embedding e.toEmbedding
  obtain ⟨B,hB⟩ := simplicial_normal_basis (v ∘ e) hu
  have hsum : (∑ j : Fin (d+1), w i (e j.succ) •
      ((v ∘ e) 0-(v ∘ e) j.succ)) = ∑ j, w i j • (v i-v j) := by
    have h := Equiv.sum_comp e (fun j => w i j • (v i-v j))
    rw [Fin.sum_univ_succ] at h
    simpa only [Function.comp_apply, he0, sub_self, smul_zero, zero_add] using h
  have hbase : rawWinningMoment (v ∘ e) (b ∘ e) 0 =
      ∑ j : Fin (d+1), w i (e j.succ) • ((v ∘ e) 0-(v ∘ e) j.succ) := by
    rw [rawWinningMoment_reindex, he0, hf i, hsum]
  have hd := simplicial_mass_flux_base_derivative (v ∘ e) (b ∘ e) (q ∘ e)
    B hB (fun j => w i (e j.succ)) hbase
  have hefun : (fun t : ℝ => winningMass (v ∘ e)
      (affinePrices (b ∘ e) (q ∘ e) t) 0) =
      (fun t : ℝ => winningMass v (affinePrices b q t) i) := by
    funext t
    change (gaussian (d+1)).real (winningCell (v ∘ e) ((affinePrices b q t) ∘ e) 0) = _
    rw [winningCell_reindex, he0]
    rfl
  have hcoeff : (∑ j : Fin (d+1), w i (e j.succ) *
      ((q ∘ e) j.succ-(q ∘ e) 0)) = -(facetLaplacian w *ᵥ q) i := by
    have h := Equiv.sum_comp e (fun j => w i j * (q j-q i))
    rw [Fin.sum_univ_succ] at h
    have hs : (∑ j : Fin (d+1), w i (e j.succ) * (q (e j.succ)-q i)) =
        ∑ j, w i j * (q j-q i) := by
      simpa only [he0, sub_self, mul_zero, zero_add] using h
    simp only [Function.comp_apply, he0]
    rw [hs, facetLaplacian_mulVec, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [hefun, hcoeff] at hd

/-- The gradient of the actual price objective, with prescribed target masses. -/
noncomputable def priceGradient {k e : ℕ} (v : Fin k → Space e)
    (p b : Fin k → ℝ) : Fin k → ℝ := fun i => p i-winningMass v b i

/-- Actual Gaussian flux is the directional derivative of the full price
gradient. The positive symmetric coefficients are constructed, not assumed. -/
theorem actual_simplicial_price_gradient_directional
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j)) ∧
      ∀ q : Fin (d+2) → ℝ,
        HasDerivAt (fun t : ℝ => priceGradient v p (affinePrices b q t))
          (facetLaplacian w *ᵥ q) 0 := by
  obtain ⟨w,hwd,hwp,hws,hf⟩ := gaussian_symmetric_positive_flux v b hv
  refine ⟨w,hwd,hwp,hws,hf,?_⟩
  intro q
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [priceGradient, neg_neg] using
    (simplicial_mass_flux_derivative v b q hv w hf i).const_sub (p i)

end GaussianFour
