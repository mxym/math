import APPTReview.PairLocalization
import APPTReview.LogAmplitude

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview

noncomputable def sparseScaleRank (L d : ℝ) : ℝ := Real.exp ((2-d)*L)
noncomputable def sparseScaleCoefficient (L d e : ℝ) : ℝ :=
  Real.sqrt e*Real.exp ((d/2-1)*L)
noncomputable def sparseScaleError (L η e : ℝ) : ℝ :=
  3*Real.sqrt e*Real.exp (-η*L)+Real.sqrt (4*e*Real.exp (-η*L))

theorem sparseScale_budget (L d e : ℝ) (he : 0≤e) :
    (sparseScaleCoefficient L d e)^2*sparseScaleRank L d=e := by
  have hx : Real.exp ((d/2-1)*L)*Real.exp ((d/2-1)*L)*Real.exp ((2-d)*L)=1 := by
    rw [← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  unfold sparseScaleCoefficient sparseScaleRank
  rw [mul_pow,Real.sq_sqrt he]
  calc
    _ = e*(Real.exp ((d/2-1)*L)*Real.exp ((d/2-1)*L)*Real.exp ((2-d)*L)) := by ring
    _ = _ := by rw [hx,mul_one]

theorem sparseScale_low_error (L d η e : ℝ) :
    sparseScaleCoefficient L d e*Real.exp ((d/2-1-η)*L)*sparseScaleRank L d=
      Real.sqrt e*Real.exp (-η*L) := by
  unfold sparseScaleCoefficient sparseScaleRank
  calc
    _ = Real.sqrt e*(Real.exp ((d/2-1)*L)*Real.exp ((d/2-1-η)*L)*Real.exp ((2-d)*L)) := by ring
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 2
      ring

theorem sparseScale_high_error (L d η e : ℝ) :
    sparseScaleCoefficient L d e/Real.exp ((d/2-1+η)*L)=
      Real.sqrt e*Real.exp (-η*L) := by
  unfold sparseScaleCoefficient
  rw [mul_div_assoc,← Real.exp_sub]
  congr 2
  ring

theorem nonneg_mul_sqrt (c x : ℝ) (hc : 0≤c) : c*Real.sqrt x=Real.sqrt (c^2*x) := by
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

/-- Exact scale cancellation; the error does not depend on the level d. -/
theorem sparseScale_normalize_bound (L d η e q Y : ℝ) (he : 0≤e)
    (hY : Y≤2*Real.exp ((d/2-1-η)*L)*sparseScaleRank L d+
      1/Real.exp ((d/2-1+η)*L)+Real.sqrt (2*sparseScaleRank L d*q)+
      Real.sqrt (4*sparseScaleRank L d*Real.exp (-η*L))) :
    sparseScaleCoefficient L d e*Y≤Real.sqrt (2*e*q)+sparseScaleError L η e := by
  let c := sparseScaleCoefficient L d e
  have hc : 0≤c := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left hY hc
  have hbudget := sparseScale_budget L d e he
  have hmid : c*Real.sqrt (2*sparseScaleRank L d*q)=Real.sqrt (2*e*q) := by
    rw [nonneg_mul_sqrt _ _ hc]
    congr 1
    change c^2*sparseScaleRank L d=e at hbudget
    calc
      _ = 2*(c^2*sparseScaleRank L d)*q := by ring
      _ = _ := by rw [hbudget]
  have hbad : c*Real.sqrt (4*sparseScaleRank L d*Real.exp (-η*L))=
      Real.sqrt (4*e*Real.exp (-η*L)) := by
    rw [nonneg_mul_sqrt _ _ hc]
    congr 1
    change c^2*sparseScaleRank L d=e at hbudget
    calc
      _ = 4*(c^2*sparseScaleRank L d)*Real.exp (-η*L) := by ring
      _ = _ := by rw [hbudget]
  have hlo := sparseScale_low_error L d η e
  have hhi := sparseScale_high_error L d η e
  change c*Real.exp ((d/2-1-η)*L)*sparseScaleRank L d=_ at hlo
  change c/Real.exp ((d/2-1+η)*L)=_ at hhi
  simp only [mul_add] at hh
  rw [hmid,hbad] at hh
  have ha : c*(2*Real.exp ((d/2-1-η)*L)*sparseScaleRank L d)=2*Real.sqrt e*Real.exp (-η*L) := by nlinarith [hlo]
  have hb : c*(1/Real.exp ((d/2-1+η)*L))=Real.sqrt e*Real.exp (-η*L) := by simpa only [mul_one_div] using hhi
  rw [ha,hb] at hh
  unfold sparseScaleError
  change c*Y≤_
  linarith

end APPTReview
