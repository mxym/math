import APPTReview.LacunaryEnergy

open scoped BigOperators
namespace APPTReview

/-- Weighted Cauchy--Schwarz with a total weight bound. -/
theorem fractional_weight_cauchy {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (r : ℝ) (hw : ∀ i∈S,0≤w i) (hw1 : ∀ i∈S,w i≤1)
    (hr : (∑ i∈S,w i)≤r) :
    (∑ i∈S,w i*y i) ≤ Real.sqrt (r*(∑ i∈S,(y i)^2)) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r:=fun i => w i*y i) (f:=w) (g:=fun i => w i*(y i)^2)
    hw (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i _ => by nlinarith [sq_nonneg (w i*y i)])
  have hq : (∑ i∈S,w i*(y i)^2) ≤ ∑ i∈S,(y i)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [hw1 i hi,sq_nonneg (y i)]
  have hp := mul_le_mul hr hq
    (Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)))
    ((Finset.sum_nonneg hw).trans hr)
  exact Real.le_sqrt_of_sq_le (hc.trans hp)

end APPTReview

namespace APPTReview

/-- Exact low/middle/high estimate, uniform over the finite index set. -/
theorem fractional_strip_localization {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (r T a b : ℝ) (hw : ∀ i∈S,0≤w i) (hw1 : ∀ i∈S,w i≤1)
    (hy : ∀ i∈S,0≤y i) (hr : (∑ i∈S,w i)≤r)
    (hT : (∑ i∈S,(y i)^2)≤T) (ha : 0≤a) (hb : 0<b) (hab : a≤b) :
    (∑ i∈S,w i*y i) ≤ a*r+T/b+
      Real.sqrt (r*(∑ i∈S.filter (fun i => a≤y i ∧ y i≤b),(y i)^2)) := by
  classical
  let M := S.filter (fun i => a≤y i ∧ y i≤b)
  have hsplit : (∑ i∈S,w i*y i)=
      (∑ i∈S,if y i<a then w i*y i else 0)+
      (∑ i∈S,if b<y i then w i*y i else 0)+(∑ i∈M,w i*y i) := by
    rw [show (∑ i∈M,w i*y i)=∑ i∈S,if a≤y i ∧ y i≤b then w i*y i else 0 by
      exact Finset.sum_filter _ _]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hlow : y i<a
    · have hhigh : ¬b<y i := by linarith
      simp [hlow,hhigh,not_le.mpr hlow]
    · by_cases hhigh : b<y i
      · simp [hlow,hhigh,not_le.mpr hhigh]
      · simp [hlow,hhigh,le_of_not_gt hlow,le_of_not_gt hhigh]
  have hlow : (∑ i∈S,if y i<a then w i*y i else 0)≤a*r := by
    calc
      _ ≤ ∑ i∈S,a*w i := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with ht
        · nlinarith [mul_nonneg (hw i hi) (sub_nonneg.mpr ht.le)]
        · exact mul_nonneg ha (hw i hi)
      _ = a*(∑ i∈S,w i) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hr ha
  have hhigh : (∑ i∈S,if b<y i then w i*y i else 0)≤T/b := by
    calc
      _ ≤ ∑ i∈S,(y i)^2/b := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with ht
        · have hwy : w i*y i≤y i := by nlinarith [hw1 i hi,hy i hi]
          exact hwy.trans ((le_div_iff₀ hb).2 (by nlinarith [hy i hi]))
        · exact div_nonneg (sq_nonneg _) hb.le
      _ = (∑ i∈S,(y i)^2)/b := (Finset.sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right hT hb.le
  have hsub : M⊆S := Finset.filter_subset _ _
  have hM : (∑ i∈M,w i)≤r :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i hi)).trans hr
  have hmid := fractional_weight_cauchy M w y r
    (fun i hi => hw i (hsub hi)) (fun i hi => hw1 i (hsub hi)) hM
  rw [hsplit]
  linarith

end APPTReview
