import BapatSphereBalance
import BapatSelectorRows
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section

def complexRealPart4 (z : EuclideanSpace ℂ (Fin 4)) : RealSpace4 :=
  WithLp.toLp 2 (fun i => (z i).re)

def complexImagPart4 (z : EuclideanSpace ℂ (Fin 4)) : RealSpace4 :=
  WithLp.toLp 2 (fun i => (z i).im)

def complexQuadratic4 (z : EuclideanSpace ℂ (Fin 4)) : ℂ := ∑ i, (z i)^2

def balanceParameter (z : EuclideanSpace ℂ (Fin 4)) : ℝ := (1+‖complexQuadratic4 z‖)/2

theorem complexQuadratic4_norm_le (z : EuclideanSpace ℂ (Fin 4)) :
    ‖complexQuadratic4 z‖ ≤ ‖z‖^2 := by
  calc
    _ ≤ ∑ i : Fin 4, ‖(z i)^2‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_pow,EuclideanSpace.norm_sq_eq]

theorem balanceParameter_mem (z : ComplexUnitSphere4) :
    1/2 ≤ balanceParameter z ∧ balanceParameter z ≤ 1 := by
  have hn := complexQuadratic4_norm_le z
  have hz : ‖(z : EuclideanSpace ℂ (Fin 4))‖=1 := by simpa using z.property
  rw [hz] at hn
  unfold balanceParameter
  constructor <;> nlinarith [norm_nonneg (complexQuadratic4 z)]

@[fun_prop] theorem balanceParameter_continuous : Continuous balanceParameter := by
  unfold balanceParameter complexQuadratic4
  fun_prop

theorem complexQuadratic4_smul (a : ℂ) (z : EuclideanSpace ℂ (Fin 4)) :
    complexQuadratic4 (a • z) = a^2 * complexQuadratic4 z := by
  simp [complexQuadratic4,PiLp.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]

theorem complex_real_imag_norm_sq (z : EuclideanSpace ℂ (Fin 4)) :
    ‖z‖^2 = ‖complexRealPart4 z‖^2 + ‖complexImagPart4 z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,complexRealPart4,complexImagPart4,WithLp.ofLp_toLp,
    Real.norm_eq_abs,sq_abs,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [← Finset.sum_add_distrib,pow_two]

theorem complexQuadratic4_re (z : EuclideanSpace ℂ (Fin 4)) :
    (complexQuadratic4 z).re = ‖complexRealPart4 z‖^2 - ‖complexImagPart4 z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  simp [complexQuadratic4,complexRealPart4,complexImagPart4,
    ← Finset.sum_sub_distrib,pow_two,Complex.mul_re]

theorem complexQuadratic4_im (z : EuclideanSpace ℂ (Fin 4)) :
    (complexQuadratic4 z).im = 2 * inner ℝ (complexRealPart4 z) (complexImagPart4 z) := by
  simp [complexQuadratic4,complexRealPart4,complexImagPart4,PiLp.inner_apply,
    RCLike.inner_apply,← Finset.mul_sum,pow_two,Complex.mul_im]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A unit phase makes the quadratic invariant real nonnegative, including when it is zero. -/
theorem exists_phase_quadratic_nonnegative (q : ℂ) :
    ∃ a : ℂ, ‖a‖=1 ∧ a^2*q=(‖q‖:ℂ) := by
  let a := Complex.exp (-((q.arg:ℂ)*Complex.I)/2)
  have ha : ‖a‖=1 := by simp [a,Complex.norm_exp,Complex.div_re,Complex.mul_re]
  have ha2 : a^2 = Complex.exp (-((q.arg:ℂ)*Complex.I)) := by
    rw [pow_two,← Complex.exp_add]
    congr 1
    ring
  refine ⟨a,ha,?_⟩
  rw [ha2]
  calc
    _ = Complex.exp (-((q.arg:ℂ)*Complex.I))*
        ((‖q‖:ℂ)*Complex.exp ((q.arg:ℂ)*Complex.I)) := by rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖q‖:ℂ)*(Complex.exp (-((q.arg:ℂ)*Complex.I))*Complex.exp ((q.arg:ℂ)*Complex.I)) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp

/-- After a unit phase, real and imaginary parts are orthogonal with the intrinsic squared lengths. -/
theorem exists_balanced_real_imag_parts (z : ComplexUnitSphere4) :
    ∃ a : ℂ, ‖a‖=1 ∧
      inner ℝ (complexRealPart4 (a • (z : EuclideanSpace ℂ (Fin 4))))
        (complexImagPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))) = 0 ∧
      ‖complexRealPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))‖^2 = balanceParameter z ∧
      ‖complexImagPart4 (a • (z : EuclideanSpace ℂ (Fin 4)))‖^2 = 1-balanceParameter z := by
  obtain ⟨a,ha,hq⟩ := exists_phase_quadratic_nonnegative (complexQuadratic4 z)
  have he : complexQuadratic4 (a • (z : EuclideanSpace ℂ (Fin 4))) = (‖complexQuadratic4 z‖:ℂ) := by
    rw [complexQuadratic4_smul,hq]
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  rw [complexQuadratic4_re] at hre
  rw [complexQuadratic4_im] at him
  simp only [Complex.ofReal_re,Complex.ofReal_im] at hre him
  have hn := complex_real_imag_norm_sq (a • (z : EuclideanSpace ℂ (Fin 4)))
  have hz : ‖(z : EuclideanSpace ℂ (Fin 4))‖=1 := by simpa using z.property
  rw [norm_smul,ha,hz] at hn
  refine ⟨a,ha,by linarith,?_,?_⟩ <;> unfold balanceParameter <;> linarith

end
end BapatRealExistence
