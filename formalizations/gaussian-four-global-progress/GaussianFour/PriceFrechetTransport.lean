import GaussianFour.PriceFrechetIntegral
import GaussianFour.PriceSecondVariation
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Transport of actual Gaussian mass Frechet derivatives and identification
with the previously derived fixed flux coefficients. -/
open MeasureTheory ProbabilityTheory Set Filter Module Matrix
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d k : ℕ} [NeZero k]

theorem winningMass_base_price_differentiableAt
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    DifferentiableAt ℝ (fun c => winningMass v c 0) b := by
  obtain ⟨B,hB⟩ := simplicial_normal_basis v hv
  obtain ⟨T,hp,hs⟩ := simplicial_winning_graph_coordinates v B hB
  let u : Fin (d+2) → Space (d+1) := fun i => T (v i)
  have hmap : DifferentiableAt ℝ
      (fun c : Fin (d+2) → ℝ => winningGraphPrices u c) b := by
    unfold winningGraphPrices
    fun_prop
  have h := (graphMass_price_differentiableAt (winningGraphSlopes u)
    (winningGraphPrices u b) hs).comp b hmap
  have he : (fun c : Fin (d+2) → ℝ => winningMass v c 0) =
      (fun c : Fin (d+2) → ℝ => graphMass (winningGraphSlopes u) (winningGraphPrices u c)) := by
    funext c
    rw [← winningMass_isometry v c T 0]
    exact winningMass_as_graph u c hp
  rw [he]
  exact h

/-- Every actual cell mass is Frechet differentiable in all price variables. -/
theorem winningMass_price_differentiableAt
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (i : Fin (d+2)) :
    DifferentiableAt ℝ (fun c => winningMass v c i) b := by
  classical
  let e : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
  have he0 : e 0 = i := Equiv.swap_apply_left 0 i
  have hu : AffineIndependent ℝ (v ∘ e) := hv.comp_embedding e.toEmbedding
  have h := (winningMass_base_price_differentiableAt (v ∘ e) (b ∘ e) hu).comp b
    (show DifferentiableAt ℝ (fun c : Fin (d+2) → ℝ => c ∘ e) b by fun_prop)
  have he : (fun c : Fin (d+2) → ℝ => winningMass (v ∘ e) (c ∘ e) 0) =
      (fun c : Fin (d+2) → ℝ => winningMass v c i) := by
    funext c
    unfold winningMass
    rw [winningCell_reindex, he0]
  rwa [he] at h

lemma priceGradient_differentiableAt
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) : DifferentiableAt ℝ (priceGradient v p) b := by
  apply differentiableAt_pi.mpr
  intro i
  exact (winningMass_price_differentiableAt v b hv i).const_sub (p i)

noncomputable def priceMatrixMap (A : Matrix (Fin k) (Fin k) ℝ) :
    (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ j, A i j •
    (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ))

@[simp] lemma priceMatrixMap_apply (A : Matrix (Fin k) (Fin k) ℝ) (q : Fin k → ℝ) :
    priceMatrixMap A q = A *ᵥ q := by
  ext i
  simp [priceMatrixMap, Matrix.mulVec, dotProduct]

noncomputable def priceCovectorMap (k : ℕ) :
    (Fin k → ℝ) →L[ℝ] ((Fin k → ℝ) →L[ℝ] ℝ) :=
  ∑ i : Fin k, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)

@[simp] lemma priceCovectorMap_apply (a q : Fin k → ℝ) :
    priceCovectorMap k a q = ∑ i, a i * q i := by
  simp [priceCovectorMap]

/-- The original integral objective has the actual mass-defect covector as
its Frechet derivative; this does not assume second differentiability. -/
theorem priceObjective_hasFDerivAt_mass_gradient
    (v : Fin k → Space d) (p b : Fin k → ℝ) (hv : Function.Injective v) :
    HasFDerivAt (priceObjective v p) (priceCovectorMap k (priceGradient v p b)) b := by
  have hf : DifferentiableAt ℝ (priceObjective v p) b :=
    (expectedScore_price_differentiableAt v b hv).add
      (show DifferentiableAt ℝ (fun c : Fin k → ℝ => ∑ i, p i*c i) b by fun_prop)
  have he : fderiv ℝ (priceObjective v p) b = priceCovectorMap k (priceGradient v p b) := by
    apply ContinuousLinearMap.ext
    intro q
    have hline := hf.hasFDerivAt.hasLineDerivAt q
    change HasDerivAt (fun t : ℝ => priceObjective v p (affinePrices b q t))
      ((fderiv ℝ (priceObjective v p) b) q) 0 at hline
    have h := hline.unique (priceObjective_directional_gradient v p b q hv)
    simpa only [priceCovectorMap_apply, mul_comm] using h
  simpa only [he] using hf.hasFDerivAt

/-- A proved Frechet derivative is identified with one fixed directional flux
matrix, rather than assuming that Gateaux differentiability suffices. -/
theorem priceGradient_hasFDerivAt_flux
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) (w : Fin (d+2) → Fin (d+2) → ℝ)
    (hd : ∀ q : Fin (d+2) → ℝ,
      HasDerivAt (fun t : ℝ => priceGradient v p (affinePrices b q t))
        (facetLaplacian w *ᵥ q) 0) :
    HasFDerivAt (priceGradient v p) (priceMatrixMap (facetLaplacian w)) b := by
  have hf := priceGradient_differentiableAt v p b hv
  have he : fderiv ℝ (priceGradient v p) b = priceMatrixMap (facetLaplacian w) := by
    apply ContinuousLinearMap.ext
    intro q
    have hline := hf.hasFDerivAt.hasLineDerivAt q
    change HasDerivAt (fun t : ℝ => priceGradient v p (affinePrices b q t))
      ((fderiv ℝ (priceGradient v p) b) q) 0 at hline
    simpa only [priceMatrixMap_apply] using hline.unique (hd q)
  simpa only [he] using hf.hasFDerivAt

end GaussianFour
