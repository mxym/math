import BapatSelectorQuartic

set_option autoImplicit false
open Set Metric
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section

def canonicalComplex4 (t : ℝ) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 ![((Real.sqrt t : ℝ) : ℂ), Complex.I * ((Real.sqrt (1-t) : ℝ) : ℂ), 0, 0]

def conjugateComplex4 (z : EuclideanSpace ℂ (Fin 4)) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun i => conj (z i))

theorem canonicalComplex4_norm {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ‖canonicalComplex4 t‖ = 1 := by
  have h := complex_four_norm_sq (canonicalComplex4 t)
  simp only [canonicalComplex4, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_zero, zero_pow (by omega : 2≠0),
    Real.sq_sqrt ht, Real.sq_sqrt (sub_nonneg.mpr ht')] at h
  change ‖canonicalComplex4 t‖^2 = t+(1-t)+0+0 at h
  nlinarith [norm_nonneg (canonicalComplex4 t)]

def canonicalSphere4 (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : ComplexUnitSphere4 :=
  ⟨canonicalComplex4 t, by simpa using canonicalComplex4_norm ht ht'⟩

theorem selectorQuartic_phase_relation {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (z : ComplexUnitSphere4)
    (heq : ‖selectorQuartic (selectorParameter t) z‖^2 = selectorProfile (selectorParameter t) t) :
    (t : ℂ) * ((z : EuclideanSpace ℂ (Fin 4)) 1)^2 =
      -((1-t : ℝ) : ℂ) * ((z : EuclideanSpace ℂ (Fin 4)) 0)^2 := by
  obtain ⟨hu,hv,_,_⟩ := selectorQuartic_equality_moduli ht ht' z heq
  let c := selectorParameter t
  let u := (z : EuclideanSpace ℂ (Fin 4)) 0
  let v := (z : EuclideanSpace ℂ (Fin 4)) 1
  have hc : 0 ≤ c := selectorParameter_nonneg ht ht'
  have ha : 0 < 1+c := by linarith
  have htr : 0 < t*(1-t) := mul_pos (by linarith) (by linarith)
  have hsq : ‖(((1+c:ℝ):ℂ)*u^2-v^2)‖^2 = (1+c*t)^2 := by
    apply mul_left_cancel₀ htr.ne'
    simpa only [selectorQuartic, norm_mul, mul_pow, hu, hv, selectorProfile] using heq
  have hd : ‖(((1+c:ℝ):ℂ)*u^2-v^2)‖ = 1+c*t := by
    have hh : 0 < 1+c*t := by nlinarith [mul_nonneg hc (show 0 ≤ t by linarith)]
    nlinarith [norm_nonneg (((1+c:ℝ):ℂ)*u^2-v^2)]
  have hnu : ‖((1+c:ℝ):ℂ)*u^2‖ = (1+c)*t := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, hu]
  have hnv : ‖-v^2‖ = 1-t := by rw [norm_neg, norm_pow, hv]
  have he : ‖((1+c:ℝ):ℂ)*u^2 + -v^2‖ =
      ‖((1+c:ℝ):ℂ)*u^2‖ + ‖-v^2‖ := by
    rw [← sub_eq_add_neg,hd,hnu,hnv]
    ring
  have hr := (norm_add_eq_iff_real (x := ((1+c:ℝ):ℂ)*u^2) (y := -v^2)).mp he
  rw [hnu,hnv] at hr
  have hr' : ((1+c:ℝ):ℂ) * (((1-t:ℝ):ℂ)*u^2+(t:ℂ)*v^2) = 0 := by
    change ((1-t:ℝ):ℂ)*(((1+c:ℝ):ℂ)*u^2) = (((1+c)*t:ℝ):ℂ)*(-v^2) at hr
    push_cast at hr ⊢
    linear_combination hr
  have haz : ((1+c:ℝ):ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hh := (mul_eq_zero.mp hr').resolve_left haz
  change (t:ℂ)*v^2 = -((1-t:ℝ):ℂ)*u^2
  linear_combination hh

/-- The only equality points are the two phase orbits of the canonical conjugate pair. -/
theorem selectorQuartic_equality_phase_orbits {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (z : ComplexUnitSphere4)
    (heq : ‖selectorQuartic (selectorParameter t) z‖^2 = selectorProfile (selectorParameter t) t) :
    ∃ a : ℂ, ‖a‖=1 ∧
      ((z : EuclideanSpace ℂ (Fin 4)) = a • canonicalComplex4 t ∨
       (z : EuclideanSpace ℂ (Fin 4)) = a • conjugateComplex4 (canonicalComplex4 t)) := by
  obtain ⟨hu,hv,h2,h3⟩ := selectorQuartic_equality_moduli ht ht' z heq
  have hrel := selectorQuartic_phase_relation ht ht' z heq
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1-t := by linarith
  have ha0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ht0).ne'
  let a : ℂ := (z : EuclideanSpace ℂ (Fin 4)) 0 / (Real.sqrt t : ℂ)
  have hrt : (Real.sqrt t : ℂ)^2 = (t:ℂ) := by exact_mod_cast Real.sq_sqrt ht0.le
  have hrr : (Real.sqrt (1-t) : ℂ)^2 = ((1-t:ℝ):ℂ) := by exact_mod_cast Real.sq_sqrt ht1.le
  have h0 : (z : EuclideanSpace ℂ (Fin 4)) 0 = a*(Real.sqrt t : ℂ) := by
    dsimp [a]; rw [div_mul_cancel₀ _ ha0]
  have hanorm : ‖a‖=1 := by
    have hu' : ‖(z : EuclideanSpace ℂ (Fin 4)) 0‖ = Real.sqrt t := by
      nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t,
        norm_nonneg ((z : EuclideanSpace ℂ (Fin 4)) 0)]
    dsimp [a]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t),hu']
    exact div_self (Real.sqrt_pos.mpr ht0).ne'
  have heqsq : ((z : EuclideanSpace ℂ (Fin 4)) 1)^2 =
      (a*(Complex.I*(Real.sqrt (1-t):ℂ)))^2 := by
    apply mul_left_cancel₀ (show (t:ℂ)≠0 by exact_mod_cast ht0.ne')
    rw [hrel,h0]
    simp only [mul_pow,hrr,Complex.I_sq,hrt]
    ring
  refine ⟨a,hanorm,?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heqsq with h1 | h1
  · left
    ext i
    fin_cases i <;> simp [canonicalComplex4, h0,h1,h2,h3]
  · right
    ext i
    fin_cases i <;> simp [canonicalComplex4,conjugateComplex4,h0,h1,h2,h3]

@[simp] theorem selectorQuartic_smul (c : ℝ) (a : ℂ) (z : EuclideanSpace ℂ (Fin 4)) :
    selectorQuartic c (a • z) = a^4 * selectorQuartic c z := by
  simp only [selectorQuartic, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] theorem selectorQuartic_conjugate (c : ℝ) (z : EuclideanSpace ℂ (Fin 4)) :
    selectorQuartic c (conjugateComplex4 z) = conj (selectorQuartic c z) := by
  simp [selectorQuartic, conjugateComplex4]

theorem selectorQuartic_canonical_value {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (c : ℝ) :
    selectorQuartic c (canonicalComplex4 t) =
      Complex.I * ((Real.sqrt t * Real.sqrt (1-t) * (1+c*t) : ℝ) : ℂ) := by
  have hrt : (Real.sqrt t : ℂ)^2 = (t:ℂ) := by exact_mod_cast Real.sq_sqrt ht
  have hrr : (Real.sqrt (1-t) : ℂ)^2 = ((1-t:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr ht')
  simp only [selectorQuartic, canonicalComplex4, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_pow, hrt, hrr, Complex.I_sq]
  push_cast
  ring

theorem selectorQuartic_canonical_attains {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (c : ℝ) :
    ‖selectorQuartic c (canonicalComplex4 t)‖^2 = selectorProfile c t := by
  rw [selectorQuartic_canonical_value ht ht', norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (sub_nonneg.mpr ht'),selectorProfile]

/-- Exact selector equality locus, with phase orbits rather than a quotient type. -/
theorem selectorQuartic_equality_iff {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (z : ComplexUnitSphere4) :
    ‖selectorQuartic (selectorParameter t) z‖^2 = selectorProfile (selectorParameter t) t ↔
      ∃ a : ℂ, ‖a‖=1 ∧
        ((z : EuclideanSpace ℂ (Fin 4)) = a • canonicalComplex4 t ∨
         (z : EuclideanSpace ℂ (Fin 4)) = a • conjugateComplex4 (canonicalComplex4 t)) := by
  refine ⟨selectorQuartic_equality_phase_orbits ht ht' z, ?_⟩
  rintro ⟨a,ha,h|h⟩
  · rw [h,selectorQuartic_smul,norm_mul,norm_pow,ha,one_pow,one_mul]
    exact selectorQuartic_canonical_attains (by linarith) (by linarith) _
  · rw [h,selectorQuartic_smul,selectorQuartic_conjugate,norm_mul,norm_pow,ha,
      one_pow,one_mul,RCLike.norm_conj]
    exact selectorQuartic_canonical_attains (by linarith) (by linarith) _

end
end BapatRealExistence
