import APPTReview.EffectiveJointScalar

namespace APPTReview

def effectiveTrace (D m h k : ℝ) : ℝ := D*effectiveBackground m h+2*h*(k+m)
noncomputable def effectivePurity (D m h k : ℝ) : ℝ :=
  (D*(effectiveBackground m h)^2+2*effectiveBackground m h*(2*h*(k+m))+
    4*h^2*(k+m^2+2*m))/(effectiveTrace D m h k)^2

/-- Exact centered second moment of a normalized perturbation of the identity. -/
theorem normalized_perturbation_excess (D b T S : ℝ) (hD : D≠0) (hz : D*b+T≠0) :
    D^2*((D*b^2+2*b*T+S)/(D*b+T)^2-1/D)=D*(D*S-T^2)/(D*b+T)^2 := by
  generalize he : D*b+T=z at *
  field_simp
  rw [← he]
  ring

theorem effectiveTrace_pos (D m h k : ℝ) (hD : 0<D) (hm : 0<m)
    (hh : 0≤h) (hk : 0≤k) : 0<effectiveTrace D m h k := by
  unfold effectiveTrace effectiveBackground
  positivity

/-- Explicit finite lower bound, with the half-rank rounding error retained. -/
theorem effectivePurity_lower (D m h k : ℝ) (hm : 2≤m) (hD : m^2≤D)
    (hh : 1≤h) (hk0 : D≤2*k) (hk1 : 2*k≤D+1)
    (hsize : 2*h^2+4*h≤m) :
    (h/(h+2))^2*(4+D/m^2) ≤ D^2*(effectivePurity D m h k-1/D) := by
  have hmP : 0<m := by linarith
  have hDP : 0<D := by nlinarith
  have hhP : 0<h := by linarith
  have hkP : 0≤k := by linarith
  have hZ := effectiveTrace_pos D m h k hDP hmP hhP.le hkP
  let d := 2*k-D
  have hd0 : 0≤d := by dsimp [d]; linarith
  have hd1 : d≤1 := by dsimp [d]; linarith
  have hm3 := mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)
  have hmd := mul_le_mul_of_nonneg_left hD (show 0≤4*m by positivity)
  have hsmall : (2*m+d)^2≤4*m*D := by nlinarith [sq_nonneg (m-2)]
  have hcent : D*(4*h^2*(k+m^2+2*m))-(2*h*(k+m))^2 ≥ D*h^2*(4*m^2+D) := by
    have he : D*(4*h^2*(k+m^2+2*m))-(2*h*(k+m))^2-D*h^2*(4*m^2+D)=
        h^2*(4*m*D-(2*m+d)^2) := by dsimp [d]; ring
    have hp := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hsmall)
    linarith
  have hround : 2*h*(k+m)≤3*h*D := by
    have hk := mul_le_mul_of_nonneg_left hk1 hhP.le
    have hd : 1+2*m≤2*D := by nlinarith [sq_nonneg (m-1)]
    have hp := mul_le_mul_of_nonneg_left hd hhP.le
    nlinarith
  have hZub : effectiveTrace D m h k≤D*((h+2)*m) := by
    have hp := mul_le_mul_of_nonneg_left hsize hDP.le
    unfold effectiveTrace effectiveBackground
    nlinarith
  have hnum : 0≤D*(D*h^2*(4*m^2+D)) := by positivity
  have hden : 0<D*((h+2)*m) := by positivity
  have hr : D*(D*h^2*(4*m^2+D))/(D*((h+2)*m))^2 ≤
      D*(D*(4*h^2*(k+m^2+2*m))-(2*h*(k+m))^2)/(effectiveTrace D m h k)^2 := by
    calc
      _ ≤ D*(D*h^2*(4*m^2+D))/(effectiveTrace D m h k)^2 :=
        div_le_div_of_nonneg_left hnum (sq_pos_of_pos hZ) (pow_le_pow_left₀ hZ.le hZub 2)
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcent hDP.le) (sq_nonneg _)
  have he : D*(D*h^2*(4*m^2+D))/(D*((h+2)*m))^2=(h/(h+2))^2*(4+D/m^2) := by
    have hh2 : h+2≠0 := by positivity
    field_simp
  rw [he] at hr
  unfold effectivePurity effectiveTrace
  rw [normalized_perturbation_excess D (effectiveBackground m h) (2*h*(k+m))
    (4*h^2*(k+m^2+2*m)) (ne_of_gt hDP) (ne_of_gt hZ)]
  exact hr

end APPTReview
