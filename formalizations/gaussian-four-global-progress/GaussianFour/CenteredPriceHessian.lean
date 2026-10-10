import GaussianFour.PriceHessian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The actual Gaussian price Hessian is invertible after fixing the additive
price gauge. No perimeter or global covariance comparison is assumed. -/
open Matrix
open GaussianMeasureBridge
namespace GaussianFour

/-- Prices with their additive constant fixed by zero sum. -/
def centeredPriceSubspace (k : ℕ) : Submodule ℝ (Fin k → ℝ) where
  carrier := {q | ∑ i, q i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (∑ i, (a i + b i)) = 0
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' := by
    intro c q hq
    change (∑ i, c * q i) = 0
    rw [← Finset.mul_sum, hq]
    simp

variable {k : ℕ} [NeZero k]

lemma centered_constant_prices_eq_zero (q : Fin k → ℝ)
    (hz : ∑ i, q i = 0) (hc : ∀ i j, q i = q j) : q = 0 := by
  funext i
  have he : (∑ j, q j) = (k : ℝ) * q i := by
    calc
      (∑ j, q j) = ∑ _j : Fin k, q i :=
        Finset.sum_congr rfl (fun j _ => hc j i)
      _ = (k : ℝ) * q i := by simp
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  exact (mul_eq_zero.mp (he.symm.trans hz)).resolve_left hk

lemma sum_facetLaplacian_mulVec (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (q : Fin k → ℝ) :
    (∑ i, (facetLaplacian w *ᵥ q) i) = 0 := by
  have he : (∑ i, ∑ j, w i j * q j) = ∑ i, ∑ j, w i j * q i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  simp only [facetLaplacian_mulVec, _root_.mul_sub, Finset.sum_sub_distrib]
  rw [he, sub_self]

/-- Strict positivity on the centered price space, rather than merely modulo
an unspecified nullspace. -/
theorem facetLaplacian_centered_positive (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j)
    (hp : ∀ i j, i ≠ j → 0 < w i j)
    (q : Fin k → ℝ) (hz : ∑ i, q i = 0) (hq : q ≠ 0) :
    0 < q ⬝ᵥ (facetLaplacian w *ᵥ q) := by
  apply facetLaplacian_quadratic_pos_of_nonconstant w hs hw hp q
  by_contra hc
  push_neg at hc
  exact hq (centered_constant_prices_eq_zero q hz hc)

noncomputable def centeredPriceHessianMap (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) :
    centeredPriceSubspace k →ₗ[ℝ] centeredPriceSubspace k where
  toFun q := ⟨facetLaplacian w *ᵥ (q : Fin k → ℝ), sum_facetLaplacian_mulVec w hs q⟩
  map_add' a b := by
    apply Subtype.ext
    change facetLaplacian w *ᵥ ((a : Fin k → ℝ) + (b : Fin k → ℝ)) =
      facetLaplacian w *ᵥ (a : Fin k → ℝ) + facetLaplacian w *ᵥ (b : Fin k → ℝ)
    exact Matrix.mulVec_add _ _ _
  map_smul' c q := by
    apply Subtype.ext
    change facetLaplacian w *ᵥ (c • (q : Fin k → ℝ)) =
      c • (facetLaplacian w *ᵥ (q : Fin k → ℝ))
    exact Matrix.mulVec_smul _ _ _

/-- The gauge-fixed Hessian is an actual invertible linear operator. -/
theorem centeredPriceHessianMap_bijective (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (hw : ∀ i j, 0 ≤ w i j)
    (hp : ∀ i j, i ≠ j → 0 < w i j) :
    Function.Bijective (centeredPriceHessianMap w hs) := by
  have hinj : Function.Injective (centeredPriceHessianMap w hs) := by
    intro a b hab
    have hv := congrArg (fun z : centeredPriceSubspace k => (z : Fin k → ℝ)) hab
    change facetLaplacian w *ᵥ (a : Fin k → ℝ) =
      facetLaplacian w *ᵥ (b : Fin k → ℝ) at hv
    let q : Fin k → ℝ := (a : Fin k → ℝ) - (b : Fin k → ℝ)
    have hz : ∑ i, q i = 0 := by
      change (∑ i, ((a : Fin k → ℝ) i - (b : Fin k → ℝ) i)) = 0
      rw [Finset.sum_sub_distrib, a.property, b.property, sub_self]
    have hzero : facetLaplacian w *ᵥ q = 0 := by
      dsimp only [q]
      rw [Matrix.mulVec_sub, hv, sub_self]
    have hquad : q ⬝ᵥ (facetLaplacian w *ᵥ q) = 0 := by
      rw [hzero, dotProduct_zero]
    have hc := (facetLaplacian_quadratic_zero_iff_constant w hs hw hp q).mp hquad
    exact Subtype.ext (sub_eq_zero.mp (centered_constant_prices_eq_zero q hz hc))
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- For the original Gaussian integral objective, a single actual flux family
supplies both the Frechet Hessian and its centered invertibility. For four
cells take d=2, so the inducing score vectors lie in the intrinsic R^3. -/
theorem actual_simplicial_price_hessian_nondegenerate {d : ℕ}
    (v : Fin (d+2) → Space (d+1)) (p b : Fin (d+2) → ℝ)
    (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      ∃ hs : ∀ i j, w i j = w j i,
        (∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i-v j)) ∧
        HasFDerivAt (fun c => fderiv ℝ (priceObjective v p) c)
          ((priceCovectorMap (d+2)).comp (priceMatrixMap (facetLaplacian w))) b ∧
        Function.Bijective (centeredPriceHessianMap w hs) := by
  obtain ⟨w,hwd,hwp,hws,hf,_hpsd,hh,_hnull⟩ := actual_simplicial_price_hessian v p b hv
  have hn (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i = j
    · subst j
      simp [hwd]
    · exact (hwp i j hij).le
  exact ⟨w,hws,hf,hh,centeredPriceHessianMap_bijective w hws hn hwp⟩

end GaussianFour
