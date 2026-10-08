import BapatCanonicalCloud
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

namespace BapatRealExistence
noncomputable section

def complexPair (x y : ℝ) : ℂ := (x:ℂ)+Complex.I*(y:ℂ)

@[simp] theorem complexPair_re (x y : ℝ) : (complexPair x y).re=x := by simp [complexPair]
@[simp] theorem complexPair_im (x y : ℝ) : (complexPair x y).im=y := by simp [complexPair]

theorem complexPair_norm_sq (x y : ℝ) : ‖complexPair x y‖^2=x^2+y^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,pow_two]

def realFourComplexPair : RealSpace4 ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℂ) where
  toFun x := WithLp.toLp 2 (complexPair (x 0) (x 1),complexPair (x 2) (x 3))
  invFun z := WithLp.toLp 2 ![z.ofLp.1.re,z.ofLp.1.im,z.ofLp.2.re,z.ofLp.2.im]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv z := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> apply Complex.ext <;> simp
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> apply Complex.ext <;> simp
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> apply Complex.ext <;> simp
  norm_map' x := by
    have he : ‖WithLp.toLp 2 (complexPair (x 0) (x 1),complexPair (x 2) (x 3))‖^2 = ‖x‖^2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2,EuclideanSpace.norm_sq_eq]
      simp [WithLp.fst,WithLp.snd,complexPair_norm_sq,Fin.sum_univ_succ]
      <;> ring
    change ‖WithLp.toLp 2 (complexPair (x 0) (x 1),complexPair (x 2) (x 3))‖ = ‖x‖
    nlinarith [norm_nonneg (WithLp.toLp 2 (complexPair (x 0) (x 1),complexPair (x 2) (x 3))),norm_nonneg x]

def transverseComplex4 : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 ![0,0,(Real.sqrt (1/2:ℝ):ℂ),Complex.I*(Real.sqrt (1/2:ℝ):ℂ)]

def complexRowRatio (t : ℝ) (v : RealSpace4) : ℂ :=
  realComplexLinear v transverseComplex4 / realComplexLinear v (canonicalComplex4 t)

def realRowRatio (t : ℝ) (v : RealSpace4) : ℝ := (complexRowRatio t v).re

def balancedRealRatio (v : RealSpace4) : ℝ :=
  ((v 2)*(v 0)+(v 3)*(v 1))/((v 0)^2+(v 1)^2)

theorem complexRowRatio_balanced (v : RealSpace4) :
    complexRowRatio (1/2) v = complexPair (v 2) (v 3) / complexPair (v 0) (v 1) := by
  have hs : (Real.sqrt (1/2:ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<1/2)).ne'
  have hn : realComplexLinear v transverseComplex4 =
      complexPair (v 2) (v 3)*(Real.sqrt (1/2:ℝ):ℂ) := by
    simp [realComplexLinear,transverseComplex4,complexPair,Fin.sum_univ_succ]
    <;> ring
  have hd : realComplexLinear v (canonicalComplex4 (1/2)) =
      complexPair (v 0) (v 1)*(Real.sqrt (1/2:ℝ):ℂ) := by
    norm_num [realComplexLinear,canonicalComplex4,complexPair,Fin.sum_univ_succ]
    change (v 0:ℂ)*(↑(Real.sqrt 2))⁻¹ + (v 1:ℂ)*(Complex.I*(↑(Real.sqrt 2))⁻¹) = _
    ring
  rw [complexRowRatio,hn,hd,mul_div_mul_right _ _ hs]

theorem realRowRatio_balanced (v : RealSpace4) : realRowRatio (1/2) v = balancedRealRatio v := by
  rw [realRowRatio,complexRowRatio_balanced,Complex.div_re]
  simp [balancedRealRatio,Complex.normSq_apply,pow_two]
  <;> ring

theorem balancedRealRatio_smul (v : RealSpace4) (r : ℝ) (hr : r≠0) :
    balancedRealRatio (r • v) = balancedRealRatio v := by
  have hn : (r*(v 2))*(r*(v 0))+(r*(v 3))*(r*(v 1)) =
      r^2*((v 2)*(v 0)+(v 3)*(v 1)) := by ring
  have hd : (r*(v 0))^2+(r*(v 1))^2=r^2*((v 0)^2+(v 1)^2) := by ring
  simp only [balancedRealRatio,PiLp.smul_apply,smul_eq_mul]
  rw [hn,hd,mul_div_mul_left _ _ (pow_ne_zero 2 hr)]

/-- The real covector giving the difference of two complex ratio real parts. -/
def ratioDifferenceCoefficient (d e : ℂ) : RealSpace4 :=
  WithLp.toLp 2 ![(d⁻¹).re,-(d⁻¹).im,-(e⁻¹).re,(e⁻¹).im]

theorem ratioDifferenceCoefficient_inner (d e : ℂ) (x : RealSpace4) :
    inner ℝ (ratioDifferenceCoefficient d e) x =
      (complexPair (x 0) (x 1)/d).re - (complexPair (x 2) (x 3)/e).re := by
  simp [ratioDifferenceCoefficient,PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,
    div_eq_mul_inv,Complex.mul_re]
  <;> ring

theorem ratioDifferenceCoefficient_norm_sq (d e : ℂ) :
    ‖ratioDifferenceCoefficient d e‖^2=‖d‖⁻¹^2+‖e‖⁻¹^2 := by
  rw [← norm_inv,← norm_inv]
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  rw [EuclideanSpace.norm_sq_eq]
  simp [ratioDifferenceCoefficient,Fin.sum_univ_succ,pow_two]
  <;> ring

theorem ratioDifferenceCoefficient_norm_le (d e : ℂ) :
    ‖ratioDifferenceCoefficient d e‖ ≤ ‖d‖⁻¹+‖e‖⁻¹ := by
  have h := ratioDifferenceCoefficient_norm_sq d e
  have hd := inv_nonneg.mpr (norm_nonneg d)
  have he := inv_nonneg.mpr (norm_nonneg e)
  nlinarith [mul_nonneg hd he,norm_nonneg (ratioDifferenceCoefficient d e)]

/-- The two radial Jacobian factors cancel the quotient singularities. -/
theorem ratioDifferenceCoefficient_radial_cancel {d e : ℂ} (hd : d≠0) (he : e≠0) :
    ‖d‖*‖e‖*‖ratioDifferenceCoefficient d e‖ = Real.sqrt (‖d‖^2+‖e‖^2) := by
  have hsq := ratioDifferenceCoefficient_norm_sq d e
  have hdn : ‖d‖≠0 := norm_ne_zero_iff.mpr hd
  have hen : ‖e‖≠0 := norm_ne_zero_iff.mpr he
  have h : (‖d‖*‖e‖*‖ratioDifferenceCoefficient d e‖)^2 = ‖d‖^2+‖e‖^2 := by
    rw [mul_pow,mul_pow,hsq]
    field_simp
    <;> ring
  have hr := Real.sq_sqrt (show 0≤‖d‖^2+‖e‖^2 by positivity)
  nlinarith [Real.sqrt_nonneg (‖d‖^2+‖e‖^2),
    show 0≤‖d‖*‖e‖*‖ratioDifferenceCoefficient d e‖ by positivity]

end
end BapatRealExistence
