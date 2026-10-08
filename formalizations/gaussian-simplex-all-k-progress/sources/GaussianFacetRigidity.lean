import GaussianFluxEnergy
import GaussianWeightedRigidity
import GaussianEquidistantRigidity

/-! The equality step of the facet Cauchy chain: positive actual face weights
force all edge lengths equal, hence the normalized Gram matrix is regular. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

theorem flux_cauchy_equality_regular (hk : 2 ≤ k) (v : Fin k → Space d)
    (w : Fin k → Fin k → ℝ) (hd : ∀ i, w i i = 0)
    (hp : ∀ i j, i ≠ j → 0 < w i j)
    (hz : ∑ i, v i = 0) (htrace : ∑ i, ‖v i‖^2 = 1)
    (he : (fluxPerimeter v w)^2 = fluxTrace w *
      ((∑ i, ∑ j, w i j * ‖v i-v j‖^2)/2)/2) :
    scoreGram v = regularCovariance k := by
  classical
  have hw (i j : Fin k) : 0 ≤ w i j := by
    by_cases hij : i = j
    · simpa [hij,hd]
    · exact (hp i j hij).le
  let r : Fin k := ⟨1,by omega⟩
  have hr : (0 : Fin k) ≠ r := by simp [r,Fin.ext_iff]
  have hW : 0 < ∑ z : Fin k × Fin k, w z.1 z.2 := by
    apply Finset.sum_pos' (fun z _ => hw z.1 z.2)
    exact ⟨(0,r),Finset.mem_univ _,hp 0 r hr⟩
  have hpair : (∑ z : Fin k × Fin k, w z.1 z.2 * ‖v z.1-v z.2‖)^2 =
      (∑ z : Fin k × Fin k, w z.1 z.2) *
        (∑ z : Fin k × Fin k, w z.1 z.2 * ‖v z.1-v z.2‖^2) := by
    simp only [Fintype.sum_prod_type]
    unfold fluxPerimeter fluxTrace at he
    nlinarith
  let a : ℝ := (∑ z : Fin k × Fin k, w z.1 z.2 * ‖v z.1-v z.2‖) /
    (∑ z : Fin k × Fin k, w z.1 z.2)
  have ha (i j : Fin k) (hij : i ≠ j) : ‖v i-v j‖ = a :=
    GaussianSimplexAlgebra.weighted_cauchy_equality_lengths Finset.univ
      (fun z : Fin k × Fin k => w z.1 z.2) (fun z => ‖v z.1-v z.2‖)
      (fun z _ => hw z.1 z.2) hW hpair (i,j) (Finset.mem_univ _) (hp i j hij)
  apply equidistant_centered_gram_regular hk v hz htrace (a^2)
  intro i j hij
  rw [ha i j hij]

end GaussianMeasureBridge
