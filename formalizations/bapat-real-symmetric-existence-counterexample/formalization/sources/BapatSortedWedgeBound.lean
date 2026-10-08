import BapatExteriorUnit
import BapatOrderedRatioScore

set_option autoImplicit false
open BapatFiniteRank BapatRankTwo.MarkedInversions

namespace BapatRealExistence
noncomputable section

def rowRatios {n : ℕ} (v : Fin n → Fin 4 → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => realRowRatio t (WithLp.toLp 2 (v i))

theorem sorted_wedge_energy_bound {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {t : ℝ} (ht : 0≤t) (ht' : t≤1)
    (hp : complexEval (formsProduct v) (canonicalComplex4 t)≠0)
    (hmono : Monotone (rowRatios v t)) :
    (rowProductModulus v (canonicalSphere4 t ht ht'))^2 * (realPairScore (rowRatios v t))^2 ≤
      rowWedgeEnergy v (canonicalSphere4 t ht ht') := by
  let u := canonicalSphere4 t ht ht'
  let ζ : Fin n → ℂ := fun i => complexRowRatio t (WithLp.toLp 2 (v i))
  have hm : Monotone (fun i => (ζ i).re) := hmono
  have hs := sorted_ratio_difference_re ζ hm
  change (∑ p ∈ originalPairs (ι := Fin n), (ζ p.2-ζ p.1)).re = realPairScore (rowRatios v t) at hs
  have hr : realPairScore (rowRatios v t) ≤ ‖∑ p ∈ originalPairs (ι := Fin n), (ζ p.2-ζ p.1)‖ := by
    rw [← hs]
    exact Complex.re_le_norm _
  have he := wedge_polynomial_contraction v (canonicalComplex4 t) transverseComplex4 hp
  have hb := exterior_contraction_bound v u
    (fun p => exteriorCoefficient (canonicalComplex4 t) transverseComplex4 p.1 p.2)
    (canonical_exteriorCoefficient_unit ht ht')
  change ‖∑ c ∈ originalPairs (ι := Fin 4), complexEval (wedgePolynomial v c.1 c.2) (canonicalComplex4 t) *
    exteriorCoefficient (canonicalComplex4 t) transverseComplex4 c.1 c.2‖^2 ≤ _ at hb
  rw [he,norm_mul,mul_pow] at hb
  change (rowProductModulus v u)^2 * ‖∑ p ∈ originalPairs (ι := Fin n), (ζ p.2-ζ p.1)‖^2 ≤ _ at hb
  exact (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (realPairScore_nonneg _) (norm_nonneg _)).mpr hr) (sq_nonneg _)).trans hb

def sortRows {n : ℕ} (v : Fin n → Fin 4 → ℝ) (t : ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => v (Tuple.sort (rowRatios v t) i)

theorem sortRows_product {n : ℕ} (v : Fin n → Fin 4 → ℝ) (t : ℝ) :
    formsProduct (sortRows v t)=formsProduct v :=
  formsProduct_comp (Tuple.sort (rowRatios v t)) v

theorem sortRows_score {n : ℕ} (v : Fin n → Fin 4 → ℝ) (t : ℝ) :
    realPairScore (rowRatios (sortRows v t) t)=realPairScore (rowRatios v t) :=
  realPairScore_perm (rowRatios v t) (Tuple.sort (rowRatios v t))

theorem sortRows_wedge_energy_bound {n : ℕ} (v : Fin n → Fin 4 → ℝ)
    {t : ℝ} (ht : 0≤t) (ht' : t≤1)
    (hp : complexEval (formsProduct v) (canonicalComplex4 t)≠0) :
    (rowProductModulus (sortRows v t) (canonicalSphere4 t ht ht'))^2 * (realPairScore (rowRatios v t))^2 ≤
      rowWedgeEnergy (sortRows v t) (canonicalSphere4 t ht ht') := by
  rw [← sortRows_score v t]
  apply sorted_wedge_energy_bound _ ht ht'
  · rwa [sortRows_product]
  · exact Tuple.monotone_sort (rowRatios v t)

end
end BapatRealExistence
