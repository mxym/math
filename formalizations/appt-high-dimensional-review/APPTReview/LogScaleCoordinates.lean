import APPTReview.FinitePairMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators NNReal
namespace APPTReview

noncomputable def schmidtScalePoint (L x : ℝ) (hL : 0<L) (hx : 0≤x) (hx1 : x≤1) :
    ScaleInterval :=
  ⟨⟨max 0 (1+2*Real.log x/L),le_max_left _ _⟩,
    by
      constructor
      · exact bot_le
      · change max (0:ℝ) (1+2*Real.log x/L)≤1
        apply max_le (by norm_num)
        have hh := div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0:ℝ)≤2) (Real.log_nonpos hx hx1)) hL.le
        linarith⟩

/-- The coordinate in [0,1] is an actual clipped logarithmic amplitude. -/
theorem schmidtScalePoint_coe (L x : ℝ) (hL : 0<L) (hx : 0≤x) (hx1 : x≤1) :
    ((schmidtScalePoint L x hL hx hx1).val:ℝ)=max 0 (1+2*Real.log x/L) := rfl

/-- Nonnegligible amplitudes and a middle product lie in one common scale band. -/
theorem schmidt_pair_in_scaleBand (L d η x y : ℝ)
    (hL : 0<L) (hη : 0≤η) (hx : 0≤x) (hy : 0≤y) (hx1 : x≤1) (hy1 : y≤1)
    (hxl : Real.exp (-(1+η)*L/2)≤x) (hyl : Real.exp (-(1+η)*L/2)≤y)
    (hlo : Real.exp ((d/2-1-η)*L)≤x*y)
    (hhi : x*y≤Real.exp ((d/2-1+η)*L)) :
    |((schmidtScalePoint L x hL hx hx1).val:ℝ)+
      ((schmidtScalePoint L y hL hy hy1).val:ℝ)-d|≤4*η := by
  have hxP : 0<x := (Real.exp_pos _).trans_le hxl
  have hyP : 0<y := (Real.exp_pos _).trans_le hyl
  have hxyP : 0<x*y := mul_pos hxP hyP
  have hlx := (Real.le_log_iff_exp_le hxP).2 hxl
  have hly := (Real.le_log_iff_exp_le hyP).2 hyl
  have hprodlo := (Real.le_log_iff_exp_le hxyP).2 hlo
  have hprodhi := (Real.log_le_iff_le_exp hxyP).2 hhi
  rw [Real.log_mul (ne_of_gt hxP) (ne_of_gt hyP)] at hprodlo hprodhi
  let u := 1+2*Real.log x/L
  let v := 1+2*Real.log y/L
  have hu : -η≤u := by
    have hh : -(1+η)≤2*Real.log x/L := (le_div_iff₀ hL).2 (by nlinarith)
    dsimp [u];linarith
  have hv : -η≤v := by
    have hh : -(1+η)≤2*Real.log y/L := (le_div_iff₀ hL).2 (by nlinarith)
    dsimp [v];linarith
  have hslo : d-2-2*η≤2*(Real.log x+Real.log y)/L :=
    (le_div_iff₀ hL).2 (by nlinarith)
  have hshi : 2*(Real.log x+Real.log y)/L≤d-2+2*η :=
    (div_le_iff₀ hL).2 (by nlinarith)
  have he : u+v=2+2*(Real.log x+Real.log y)/L := by dsimp [u,v];ring
  have hcux : u≤max 0 u := le_max_right _ _
  have hcvx : v≤max 0 v := le_max_right _ _
  have hcu : max 0 u≤u+η := max_le (by linarith) (by linarith)
  have hcv : max 0 v≤v+η := max_le (by linarith) (by linarith)
  rw [schmidtScalePoint_coe,schmidtScalePoint_coe]
  change |max 0 u+max 0 v-d|≤4*η
  apply abs_le.2
  constructor <;> linarith

end APPTReview
