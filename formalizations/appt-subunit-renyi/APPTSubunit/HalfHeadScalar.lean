import APPTSubunit.HalfHeadPolynomial
import APPTReview.EntropyHead

namespace APPTSubunit
open APPTReview

noncomputable def halfEntropyKernel (x : ℝ) : ℝ := 2*(Real.sqrt (1+x)-1)^2
noncomputable def halfEntropyGap (x : ℝ) : ℝ := x^2/2-halfEntropyKernel x

theorem halfEntropyGap_lower (a : ℝ) (ha : 0≤a) :
    a^3/(4+3*a)≤halfEntropyGap a := by
  let u := Real.sqrt (1+a)-1
  have hsq : (Real.sqrt (1+a))^2=1+a := Real.sq_sqrt (by linarith)
  have hroot : 1≤Real.sqrt (1+a) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤1+a by linarith)
    simpa only [Real.sqrt_one] using h
  have hu : 0≤u := by dsimp [u];linarith
  have haeq : a=u^2+2*u := by dsimp [u];nlinarith
  have hgap : halfEntropyGap a=u^3*(u+4)/2 := by
    unfold halfEntropyGap halfEntropyKernel
    change a^2/2-2*u^2=u^3*(u+4)/2
    rw [haeq]
    ring
  have hden : 0<4+3*a := by linarith
  apply (div_le_iff₀ hden).2
  rw [hgap,haeq]
  have hp : 0≤u^4*(u^2+6*u+4)/2 := by positivity
  nlinarith

theorem halfEntropyGap_nonneg (a : ℝ) (ha : 0≤a) : 0≤halfEntropyGap a :=
  (by positivity : 0≤a^3/(4+3*a)).trans (halfEntropyGap_lower a ha)

/-- A scalar inequality established by seven exact rational polynomial cells.
The certificate includes the entire continuum, not sampled parameter values. -/
theorem half_head_rational_comparison (a r : ℝ) (ha : 0≤a) (hr : 0≤r)
    (hr1 : r≤1) (hasize : a≤2*r) :
    2*(1+r^2)^2/(1+r)^2+a*(1-r^2)-a^3/(4+3*a)≤2 := by
  by_cases hz : r=0
  · have haz : a=0 := by linarith
    simp [hz,haz]
  · have hrP : 0<r := lt_of_le_of_ne hr (Ne.symm hz)
    let t := a/(2*r)
    have ht0 : 0≤t := by dsimp [t];positivity
    have ht1 : t≤1 := by dsimp [t];exact (div_le_iff₀ (by positivity : 0<2*r)).2 (by simpa using hasize)
    have hQ := halfHeadPolynomial_nonneg r t hr hr1 ht0 ht1
    have hat : a=2*r*t := by dsimp [t];field_simp
    have hp : 0≤r*halfHeadPolynomial r t := mul_nonneg hr hQ
    have hden1 : 0<(1+r)^2 := sq_pos_of_pos (by linarith)
    have hden2 : 0<4+3*a := by linarith
    have he : (2-(2*(1+r^2)^2/(1+r)^2+a*(1-r^2)-a^3/(4+3*a)))*
        ((1+r)^2*(4+3*a))=r*halfHeadPolynomial r t := by
      field_simp
      rw [hat]
      unfold halfHeadPolynomial
      ring
    have hprod : 0≤(2-(2*(1+r^2)^2/(1+r)^2+a*(1-r^2)-a^3/(4+3*a)))*
        ((1+r)^2*(4+3*a)) := by rw [he];exact hp
    have hh := nonneg_of_mul_nonneg_left hprod (mul_pos hden1 hden2)
    linarith

theorem half_head_scalar_comparison (a r : ℝ) (ha : 0≤a) (hr : 0≤r)
    (hr1 : r≤1) (hasize : a≤2*r) :
    2*(1+r^2)^2/(1+r)^2+a*(1-r^2)-halfEntropyGap a≤2 := by
  have hh := half_head_rational_comparison a r ha hr hr1 hasize
  have hg := halfEntropyGap_lower a ha
  linarith

/-- The exact negative-side coefficient, with the square-root endpoint included. -/
theorem half_kernel_negative_bounded (z y : ℝ) (_hz : 0≤z) (hzy : z≤y) (hy : y≤1) :
    halfEntropyKernel (-z)≤(2/(1+Real.sqrt (1-y))^2)*z^2 := by
  let q := Real.sqrt (1-z)
  let p := Real.sqrt (1-y)
  have hq0 : 0≤q := Real.sqrt_nonneg _
  have hp0 : 0≤p := Real.sqrt_nonneg _
  have hqp : p≤q := Real.sqrt_le_sqrt (by linarith)
  have hq2 : q^2=1-z := Real.sq_sqrt (by linarith)
  have hqP : 0<(1+q)^2 := sq_pos_of_pos (by linarith)
  have hpP : 0<(1+p)^2 := sq_pos_of_pos (by linarith)
  have hid : halfEntropyKernel (-z)=2*z^2/(1+q)^2 := by
    apply (eq_div_iff (ne_of_gt hqP)).2
    unfold halfEntropyKernel
    change 2*(q-1)^2*(1+q)^2=2*z^2
    calc
      _ = 2*((q-1)*(1+q))^2 := by ring
      _ = 2*(-z)^2 := by congr 2;nlinarith
      _ = _ := by ring
  rw [hid]
  have hh := div_le_div_of_nonneg_left (by positivity : 0≤2*z^2) hpP
    (show (1+p)^2≤(1+q)^2 by nlinarith)
  simpa only [mul_div_assoc,div_mul_eq_mul_div] using hh

end APPTSubunit
