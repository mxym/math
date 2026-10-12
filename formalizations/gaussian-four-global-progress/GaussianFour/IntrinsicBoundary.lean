import GaussianFour.IntrinsicFlux
import GaussianFour.LaplacianQuadratic

/-! Matrix convergence of actual intrinsic Gaussian facet coefficients.
This is a boundary theorem, not the missing global variational exclusion. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

noncomputable def intrinsicLaplacian (v : Fin k → Space (d+1)) (b : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := facetLaplacian (intrinsicPairWeight v b)

lemma continuous_facetLaplacian :
    Continuous (facetLaplacian : (Fin k → Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [facetLaplacian, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The entire matrix, not just selected entries, is continuous at each
positive-mass diagram. -/
theorem continuousAt_intrinsicLaplacian
    (v : Fin k → Space (d+1)) (b : Fin k → ℝ)
    (hmass : ∀ l, 0 < (gaussian (d+1)).real (winningCell v b l)) :
    ContinuousAt (fun z : ChartParameters d k => intrinsicLaplacian z.1 z.2) (v,b) := by
  have hw : ContinuousAt (fun z : ChartParameters d k => intrinsicPairWeight z.1 z.2) (v,b) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_intrinsicPairWeight v b hmass i j
  exact continuous_facetLaplacian.continuousAt.comp hw

/-- Actual full-rank Gaussian flux passes to a distinct-score balanced limit;
its Laplacian converges and remains positive semidefinite. -/
theorem balanced_simplicial_limit_laplacian
    (vSeq : ℕ → Fin (d+2) → Space (d+1)) (bSeq : ℕ → Fin (d+2) → ℝ)
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ) (p : Fin (d+2) → ℝ)
    (hp : ∀ i, 0 < p i)
    (hv : Tendsto vSeq atTop (𝓝 v)) (hb : Tendsto bSeq atTop (𝓝 b))
    (hvn : ∀ n, AffineIndependent ℝ (vSeq n)) (hv0 : Function.Injective v)
    (hbalance : ∀ n i, (gaussian (d+1)).real (winningCell (vSeq n) (bSeq n) i) = p i) :
    (∀ i, (gaussian (d+1)).real (winningCell v b i) = p i) ∧
    (∀ i, rawWinningMoment v b i = ∑ j, intrinsicPairWeight v b i j • (v i-v j)) ∧
    (intrinsicLaplacian v b).PosSemidef ∧
    Tendsto (fun n => intrinsicLaplacian (vSeq n) (bSeq n)) atTop
      (𝓝 (intrinsicLaplacian v b)) := by
  obtain ⟨hm,hf,hs⟩ := balanced_simplicial_limit_intrinsic_flux
    vSeq bSeq v b p hp hv hb hvn hv0 hbalance
  have hpos (i : Fin (d+2)) : 0 < (gaussian (d+1)).real (winningCell v b i) := by
    rw [hm i]; exact hp i
  refine ⟨hm,hf,?_,?_⟩
  · exact facetLaplacian_posSemidef _ hs (intrinsicPairWeight_nonneg v b hpos)
  · exact Filter.Tendsto.comp
      (g := fun z : ChartParameters d (d+2) => intrinsicLaplacian z.1 z.2)
      (f := fun n : ℕ => (vSeq n,bSeq n))
      (continuousAt_intrinsicLaplacian v b hpos).tendsto (hv.prodMk_nhds hb)

end GaussianFour
