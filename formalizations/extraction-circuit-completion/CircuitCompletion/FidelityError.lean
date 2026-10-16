import SpectralProtocol.MassLower
import RankSupport.ExactEffect

open scoped BigOperators ComplexOrder
open Matrix
namespace CircuitCompletion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pureMatrix (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)
def vectorSquare (v : ι → ℂ) : ℝ := ∑ i,Complex.normSq (v i)
def squaredDistance (u v : ι → ℂ) : ℝ := vectorSquare (v-u)

theorem pureMatrix_trace (v : ι → ℂ) : (pureMatrix v).trace=(vectorSquare v:ℂ) := by
  simp only [pureMatrix,Matrix.trace_vecMulVec,dotProduct,vectorSquare,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.mul_conj _

theorem pureMatrix_idempotent (u : ι → ℂ) (hu : vectorSquare u=1) :
    pureMatrix u*pureMatrix u=pureMatrix u := by
  have hd : star u ⬝ᵥ u=1 := by
    rw [dotProduct_comm]
    change (pureMatrix u).trace=1
    rw [pureMatrix_trace,hu,Complex.ofReal_one]
  rw [pureMatrix,Matrix.vecMulVec_mul_vecMulVec,hd,one_smul]

theorem pureMatrix_pair_trace (u v : ι → ℂ) :
    (pureMatrix u*pureMatrix v).trace.re=Complex.normSq (star u ⬝ᵥ v) := by
  have hs : u ⬝ᵥ star v=star (star u ⬝ᵥ v) := by
    simp only [dotProduct,star_sum,star_mul,star_star,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [pureMatrix,pureMatrix,Matrix.vecMulVec_mul_vecMulVec,Matrix.trace_vecMulVec,
    dotProduct_smul,smul_eq_mul,hs]
  exact congrArg Complex.re (Complex.mul_conj (star u ⬝ᵥ v))

theorem squaredDistance_unit_vectors (u v : ι → ℂ)
    (hu : vectorSquare u=1) (hv : vectorSquare v=1) :
    squaredDistance u v=2-2*(star u ⬝ᵥ v).re := by
  have hs : (∑ i,(v i*star (u i)).re)=(star u ⬝ᵥ v).re := by
    simp only [dotProduct,Complex.re_sum,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  simp only [squaredDistance,vectorSquare,Pi.sub_apply,Complex.normSq_sub,
    starRingEnd_apply,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  change vectorSquare v+vectorSquare u-2*(∑ i,(v i*star (u i)).re)=_
  rw [hu,hv,hs]
  ring

/-- A complete physical fidelity effect exact on u stays near one on every
nearby unit vector. No trace-norm contraction theorem is assumed. -/
theorem exact_effect_fidelity_lower (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : (1-M).PosSemidef)
    (u v : ι → ℂ) (hu : vectorSquare u=1) (hv : vectorSquare v=1)
    (hexact : (M*pureMatrix u).trace.re=1) :
    1-squaredDistance u v ≤ (M*pureMatrix v).trace.re := by
  have hPu : (pureMatrix u).PosSemidef := Matrix.posSemidef_vecMulVec_self_star u
  have hPv : (pureMatrix v).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have htu : (pureMatrix u).trace=1 := by rw [pureMatrix_trace,hu,Complex.ofReal_one]
  have hfix := ExtractionRankSupport.exact_density_effect_fixes_density M _ hI ⟨hPu,htu⟩ hexact
  have hMP := SpectralProtocol.effect_sub_projection_posSemidef M (pureMatrix u) hM
    hPu.isHermitian (pureMatrix_idempotent u hu) hfix
  have hpair := Extraction.positive_product_trace_re (M-pureMatrix u) (pureMatrix v) hMP hPv
  simp only [Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re,pureMatrix_pair_trace] at hpair
  rw [squaredDistance_unit_vectors u v hu hv]
  let z := star u ⬝ᵥ v
  have hz : z.re^2 ≤ Complex.normSq z := by
    change z.re^2 ≤ z.re*z.re+z.im*z.im
    nlinarith [sq_nonneg z.im]
  have hquad : 2*z.re-1 ≤ z.re^2 := by nlinarith [sq_nonneg (z.re-1)]
  change 1-(2-2*z.re) ≤ _
  linarith

theorem exact_effect_fidelity_lower_delta (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : (1-M).PosSemidef)
    (u v : ι → ℂ) (hu : vectorSquare u=1) (hv : vectorSquare v=1)
    (hexact : (M*pureMatrix u).trace.re=1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : squaredDistance u v ≤ δ^2) :
    1-2*δ ≤ (M*pureMatrix v).trace.re := by
  by_cases hδ2 : δ ≤ 2
  · have h := exact_effect_fidelity_lower M hM hI u v hu hv hexact
    nlinarith
  · have h := Extraction.positive_product_trace_re M (pureMatrix v) hM
      (Matrix.posSemidef_vecMulVec_self_star v)
    linarith

end CircuitCompletion
