import APPTReview.AsymptoticUpper
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators
namespace APPTReview

/-- Exact interval second-moment inequality, retaining total bulk mass. -/
theorem interval_square_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (b r : ℝ) (hl : ∀ i∈s, b≤f i) (hu : ∀ i∈s, f i≤r*b) :
    (∑ i∈s, (f i)^2) ≤ (r+1)*b*(∑ i∈s, f i)-(s.card:ℝ)*r*b^2 := by
  have ht (i) (hi : i∈s) : (f i)^2≤(r+1)*b*f i-r*b^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr (hl i hi)) (sub_nonneg.mpr (hu i hi))
    nlinarith
  have hs := Finset.sum_le_sum ht
  simpa [Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc] using hs

/-- Complete the square without assuming a value of the optimizing interval. -/
theorem interval_moment_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (b r : ℝ) (hb : 0≤b) (hr : 0<r) (hL : 0<s.card)
    (hl : ∀ i∈s, b≤f i) (hu : ∀ i∈s, f i≤r*b)
    (hmass : (∑ i∈s, f i)≤1) :
    (∑ i∈s, (f i)^2) ≤ (r+1)^2/(4*r*(s.card:ℝ)) := by
  have hLR : (0:ℝ)<s.card := by exact_mod_cast hL
  have hcoeff : 0≤(r+1)*b := mul_nonneg (by linarith) hb
  have hx := interval_square_sum s f b r hl hu
  have hm := mul_le_mul_of_nonneg_left hmass hcoeff
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*r*(s.card:ℝ))).2
  have hs := sq_nonneg (2*r*(s.card:ℝ)*b-(r+1))
  have hd := mul_le_mul_of_nonneg_left (hx.trans (by nlinarith :
    (r+1)*b*(∑ i∈s, f i)-(s.card:ℝ)*r*b^2≤(r+1)*b-(s.card:ℝ)*r*b^2))
    (show 0≤4*r*(s.card:ℝ) by positivity)
  nlinarith

/-- Bound exceptional eigenvalues individually rather than discard them. -/
theorem bulk_exception_moment {D : ℕ} (s : Finset (Fin D)) (f : Fin D → ℝ)
    (b r B : ℝ) (hb : 0≤b) (hr : 0<r) (hB : 0≤B) (hL : 0<s.card)
    (hf : ∀ i, 0≤f i) (hs : (∑ i, f i)=1) (hmax : ∀ i, f i≤B)
    (hl : ∀ i∈s, b≤f i) (hu : ∀ i∈s, f i≤r*b) :
    (∑ i, (f i)^2) ≤ (r+1)^2/(4*r*(s.card:ℝ))+
      ((D:ℝ)-(s.card:ℝ))*B^2 := by
  classical
  have hmass : (∑ i∈s, f i)≤1 := by
    rw [← hs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hf i)
  have hbulk := interval_moment_bound s f b r hb hr hL hl hu hmass
  have htail : (∑ i∈sᶜ, (f i)^2)≤((D:ℝ)-(s.card:ℝ))*B^2 := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈sᶜ) =>
      pow_le_pow_left₀ (hf i) (hmax i) 2)
    have hc : (sᶜ.card:ℝ)=(D:ℝ)-(s.card:ℝ) := by
      have hsz : s.card≤D := by simpa using Finset.card_le_card (Finset.subset_univ s)
      simp only [Finset.card_compl, Fintype.card_fin, Nat.cast_sub hsz]
    simpa [hc] using hh
  have he := Finset.sum_add_sum_compl s (fun i => (f i)^2)
  linarith

end APPTReview

namespace APPTReview
/-- A dimension-scaled bulk bound with an explicit exceptional-rank error. -/
theorem bulk_rescale_bound (D L C K p : ℝ)
    (hD : 0<D) (hL : 0<L) (hCL : 0≤C) (hC : C≤2)
    (hLD : L≤D) (hDL : D≤2*L) (hK : D-L≤K)
    (hp : p≤C/L+9*(D-L)/D^2) :
    D*p≤C+13*K/D := by
  have hq : 0≤D-L := sub_nonneg.mpr hLD
  have hfrac : C/L≤4/D := by
    apply (div_le_div_iff₀ hL hD).2
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hfrac hq
  have he : D*(C/L+9*(D-L)/D^2)=C+(C/L)*(D-L)+9*(D-L)/D := by
    field_simp
    ring
  have hu := mul_le_mul_of_nonneg_left hp hD.le
  rw [he] at hu
  have herr : 13*(D-L)/D≤13*K/D :=
    div_le_div_of_nonneg_right (by linarith) hD.le
  calc
    D*p ≤ C+(C/L)*(D-L)+9*(D-L)/D := hu
    _ ≤ C+(4/D)*(D-L)+9*(D-L)/D := by linarith
    _ = C+13*(D-L)/D := by ring
    _ ≤ C+13*K/D := by linarith
end APPTReview
