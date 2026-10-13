import APPTReview.WeightedLocalization
import APPTReview.FiniteScaleMeasure

open scoped BigOperators NNReal
open MeasureTheory Set
namespace APPTReview
attribute [local instance] Classical.propDecidable

/-- Exact unit-vector pair mass, with ordered pairs and diagonals included. -/
theorem pair_square_mass {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs : (∑ i,(s i)^2)=1) : (∑ z : ι × ι,(s z.1*s z.2)^2)=1 := by
  simp only [mul_pow,Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul,hs,mul_one]

/-- The mass lost when either endpoint is discarded is at most twice the
single-coordinate lost mass. No cardinality or distinct-location assumption. -/
theorem pair_bad_mass {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) (G : Finset ι) :
    (∑ z : ι × ι, if z.1∈G ∧ z.2∈G then 0 else p z.1*p z.2) ≤
      2*∑ i, if i∈G then 0 else p i := by
  let b : ι → ℝ := fun i => if i∈G then 0 else p i
  have hb (z : ι × ι) : (if z.1∈G ∧ z.2∈G then 0 else p z.1*p z.2) ≤
      b z.1*p z.2+p z.1*b z.2 := by
    dsimp [b]
    by_cases h1 : z.1∈G <;> by_cases h2 : z.2∈G <;>
      simp [h1,h2] <;> nlinarith [mul_nonneg (hp z.1) (hp z.2)]
  have hh := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => hb z)
  simp only [Finset.sum_add_distrib,Fintype.sum_prod_type,
    ← Finset.mul_sum,← Finset.sum_mul,hs,one_mul,mul_one] at hh
  change _ ≤ 2*∑ i,b i
  rw [Fintype.sum_prod_type]
  linarith

/-- Finite localization into a band of the SAME actual probability measure.
The band implication is explicit here and will be proved by logarithmic scales.
Fractional weights are allowed, including weights from projection compression. -/
theorem weighted_pair_band_bound {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1)
    (t : ι → ScaleInterval) (G : Finset ι) (w : ι × ι → ℝ)
    (r a b τ d η : ℝ) (hr : 0≤r) (ha : 0≤a) (hb : 0<b) (hab : a≤b)
    (hw : ∀ z,0≤w z) (hw1 : ∀ z,w z≤1) (hwr : (∑ z,w z)≤2*r)
    (hbad : (∑ i,if i∈G then 0 else (s i)^2)≤τ)
    (hband : ∀ i j, i∈G → j∈G → a≤s i*s j → s i*s j≤b →
      |((t i).val:ℝ)+((t j).val:ℝ)-d|≤η) :
    (∑ z,w z*(s z.1*s z.2)) ≤ 2*a*r+1/b+
      Real.sqrt (2*r*((scaleLift (finiteScaleProbability (fun i => (s i)^2) t
        (fun i => sq_nonneg _) hs)).prod
        (scaleLift (finiteScaleProbability (fun i => (s i)^2) t
        (fun i => sq_nonneg _) hs))).toMeasure.real (scaleBand d η))+
      Real.sqrt (4*r*τ) := by
  classical
  let U : Finset (ι × ι) := Finset.univ
  let F := U.filter (fun z => z.1∈G ∧ z.2∈G)
  let H := U.filter (fun z => ¬(z.1∈G ∧ z.2∈G))
  let y : ι × ι → ℝ := fun z => s z.1*s z.2
  have hy (z : ι × ι) : 0≤y z := mul_nonneg (hs0 _) (hs0 _)
  have hFsub : F⊆U := Finset.filter_subset _ _
  have hHsub : H⊆U := Finset.filter_subset _ _
  have hFmass : (∑ z∈F,w z)≤2*r :=
    (Finset.sum_le_sum_of_subset_of_nonneg hFsub (fun z _ _ => hw z)).trans hwr
  have hHmass : (∑ z∈H,w z)≤2*r :=
    (Finset.sum_le_sum_of_subset_of_nonneg hHsub (fun z _ _ => hw z)).trans hwr
  have hyall : (∑ z∈U,(y z)^2)=1 := pair_square_mass s hs
  have hyF : (∑ z∈F,(y z)^2)≤1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hFsub (fun z _ _ => sq_nonneg _)).trans_eq hyall
  have hlow := fractional_strip_localization F w y (2*r) 1 a b
    (fun z _ => hw z) (fun z _ => hw1 z) (fun z _ => hy z) hFmass hyF ha hb hab
  have hHsq : (∑ z∈H,(y z)^2)≤2*τ := by
    have he : (∑ z∈H,(y z)^2)=∑ z : ι × ι,
        if z.1∈G ∧ z.2∈G then 0 else (s z.1)^2*(s z.2)^2 := by
      simp only [H,U,Finset.sum_filter,y,mul_pow]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> rfl
    rw [he]
    exact (pair_bad_mass (fun i => (s i)^2) (fun i => sq_nonneg _) hs G).trans
      (mul_le_mul_of_nonneg_left hbad (by norm_num))
  have hhigh := fractional_weight_cauchy H w y (2*r)
    (fun z _ => hw z) (fun z _ => hw1 z) hHmass
  have hhigh' : (∑ z∈H,w z*y z)≤Real.sqrt (4*r*τ) := by
    refine hhigh.trans (Real.sqrt_le_sqrt ?_)
    nlinarith [mul_le_mul_of_nonneg_left hHsq (show 0≤2*r by positivity)]
  rw [finiteScaleProbability_band]
  have hmid : (∑ z∈F.filter (fun z => a≤y z ∧ y z≤b),(y z)^2) ≤
      ∑ z : ι × ι, if |((t z.1).val:ℝ)+((t z.2).val:ℝ)-d|≤η
        then (s z.1)^2*(s z.2)^2 else 0 := by
    simp only [F,U,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    split_ifs with hgood hB hB
    · simp [y,mul_pow]
    · exact False.elim (hB (hband _ _ hgood.1.1 hgood.1.2 hgood.2.1 hgood.2.2))
    · positivity
    · rfl
  have hmiddle := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hmid (show 0≤2*r by positivity))
  have hsplit : (∑ z,w z*y z)=(∑ z∈F,w z*y z)+(∑ z∈H,w z*y z) := by
    exact (Finset.sum_filter_add_sum_filter_not U _ _).symm
  change (∑ z,w z*y z)≤_
  rw [hsplit]
  linarith

end APPTReview
