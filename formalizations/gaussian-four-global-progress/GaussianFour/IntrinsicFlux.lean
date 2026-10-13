import GaussianFour.IntrinsicContinuity
import GaussianFour.PriceMassDifferential

/-! Identification with the constructed simplicial flux and passage of the
actual Bochner flux identity through positive-mass singular limits. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

lemma simplicial_intrinsicWeight_eq_flux
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ) (hv : AffineIndependent ℝ v)
    (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hf : ∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j))
    (i j : Fin (d+2)) (hij : i ≠ j) : intrinsicPairWeight v b i j = w i j := by
  classical
  let q : Fin (d+2) → ℝ := fun l => if l = j then 1 else 0
  have h := simplicial_mass_flux_derivative v b q hv w hf i
  have hp (t : ℝ) : affinePrices b q t = coordinateShift b j t := by
    funext l
    by_cases hl : l = j <;> simp [affinePrices, coordinateShift, q, hl]
  simp_rw [hp] at h
  have hc : -(facetLaplacian w *ᵥ q) i = w i j := by
    rw [facetLaplacian_mulVec]
    simp [q, hij, Finset.sum_neg_distrib]
  rw [hc] at h
  simp only [intrinsicPairWeight, hij, ↓reduceIte, h.deriv]

/-- The intrinsic coefficients are exactly the already constructed positive
symmetric Gaussian flux family at each affine-independent diagram. -/
theorem actual_simplicial_intrinsic_coefficients
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ) (hv : AffineIndependent ℝ v) :
    (∀ i, rawWinningMoment v b i = ∑ j, intrinsicPairWeight v b i j • (v i-v j)) ∧
    (∀ i j, intrinsicPairWeight v b i j = intrinsicPairWeight v b j i) ∧
    (∀ i j, i ≠ j → 0 < intrinsicPairWeight v b i j) := by
  obtain ⟨w,hwd,hwp,hws,hf⟩ := gaussian_symmetric_positive_flux v b hv
  have he (i j : Fin (d+2)) : intrinsicPairWeight v b i j = w i j := by
    by_cases hij : i = j
    · subst j; rw [intrinsicPairWeight_diagonal, hwd]
    · exact simplicial_intrinsicWeight_eq_flux v b hv w hf i j hij
  simp_rw [he]
  exact ⟨hf,hws,hwp⟩

/-- Both the first-moment flux identity and coefficient symmetry survive a
possibly rank-deficient limit of actual balanced simplicial diagrams. -/
theorem balanced_simplicial_limit_intrinsic_flux
    (vSeq : ℕ → Fin (d+2) → Space (d+1)) (bSeq : ℕ → Fin (d+2) → ℝ)
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ) (p : Fin (d+2) → ℝ)
    (hp : ∀ i, 0 < p i)
    (hv : Tendsto vSeq atTop (𝓝 v)) (hb : Tendsto bSeq atTop (𝓝 b))
    (hvn : ∀ n, AffineIndependent ℝ (vSeq n)) (hv0 : Function.Injective v)
    (hbalance : ∀ n i, (gaussian (d+1)).real (winningCell (vSeq n) (bSeq n) i) = p i) :
    (∀ i, (gaussian (d+1)).real (winningCell v b i) = p i) ∧
    (∀ i, rawWinningMoment v b i = ∑ j, intrinsicPairWeight v b i j • (v i-v j)) ∧
    (∀ i j, intrinsicPairWeight v b i j = intrinsicPairWeight v b j i) := by
  obtain ⟨hm,hw⟩ := balanced_intrinsic_weights_limit vSeq bSeq v b p hp hv hb hv0 hbalance
  have hcoeff (n : ℕ) := actual_simplicial_intrinsic_coefficients (vSeq n) (bSeq n) (hvn n)
  refine ⟨hm, ?_, ?_⟩
  · intro i
    have hmoment : Tendsto (fun n => rawWinningMoment (vSeq n) (bSeq n) i) atTop
        (𝓝 (rawWinningMoment v b i)) := Filter.Tendsto.comp
      (g := fun z : ChartParameters d (d+2) => rawWinningMoment z.1 z.2 i)
      (f := fun n : ℕ => (vSeq n,bSeq n))
      (continuousAt_rawWinningMoment v b hv0 i).tendsto (hv.prodMk_nhds hb)
    have hright : Tendsto (fun n => ∑ j, intrinsicPairWeight (vSeq n) (bSeq n) i j •
        (vSeq n i-vSeq n j)) atTop
        (𝓝 (∑ j, intrinsicPairWeight v b i j • (v i-v j))) := by
      apply tendsto_finsetSum
      intro j _
      exact (hw i j).smul ((tendsto_pi_nhds.mp hv i).sub (tendsto_pi_nhds.mp hv j))
    have hleft := hmoment.congr' (Eventually.of_forall fun n => (hcoeff n).1 i)
    exact tendsto_nhds_unique hleft hright
  · intro i j
    have hleft := (hw i j).congr' (Eventually.of_forall fun n => (hcoeff n).2.1 i j)
    exact tendsto_nhds_unique hleft (hw j i)

end GaussianFour
