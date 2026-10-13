import APPTReview.FiniteProbability
import APPTReview.BaselineGraph

open scoped BigOperators NNReal
open MeasureTheory Set
namespace APPTReview

/-- The finite atomic measure is the actual distribution of the scale coordinates. -/
theorem scaleLift_atomic {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (x : ι → ScaleInterval) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) :
    (scaleLift (finiteAtomicProbability p x hp hs)).toMeasure=
      finiteAtomicMeasure p (fun i => (x i).val) := by
  exact finiteAtomicMeasure_map p x (fun t : ScaleInterval => t.val) measurable_subtype_coe

/-- Exact empirical two-coordinate band mass, with no assumption of distinct atoms. -/
theorem atomic_scaleBand_mass {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (x : ι → ScaleInterval) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) (d t : ℝ) :
    (scaleLift (finiteAtomicProbability p x hp hs) |>.prod
      (scaleLift (finiteAtomicProbability p x hp hs))).toMeasure.real (scaleBand d t)=
      ∑ i, ∑ j, (if |((x i).val:ℝ)+((x j).val:ℝ)-d|≤t then p i*p j else 0) := by
  classical
  rw [ProbabilityMeasure.toMeasure_prod,scaleLift_atomic p x hp hs,
    finiteAtomicMeasure_prod p p _ _ hp hp,
    finiteAtomicMeasure_real (fun z : ι×ι => p z.1*p z.2) (fun z : ι×ι => ((x z.1).val,(x z.2).val)) (fun z => mul_nonneg (hp z.1) (hp z.2))]
  simp only [Fintype.sum_prod_type,scaleBand,Set.mem_setOf_eq]

/-- Splitting a symmetric finite matrix into diagonal and the two half triangles. -/
theorem symmetric_pair_sum {m : ℕ} (F : Fin m → Fin m → ℝ)
    (hF : ∀ i j,F i j=F j i) :
    (∑ i,∑ j,F i j)=(∑ i,F i i)+2*(∑ p : UpperPair m,F p.val.1 p.val.2) := by
  have hs := (squareSlotEquiv m).sum_comp (fun p : Fin m×Fin m => F p.1 p.2)
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type] at hs
  change (∑ i,F i i)+((∑ p : UpperPair m,F p.val.1 p.val.2)+
    (∑ p : UpperPair m,F p.val.2 p.val.1))=∑ p : Fin m×Fin m,F p.1 p.2 at hs
  have he : (∑ p : UpperPair m,F p.val.2 p.val.1)=∑ p : UpperPair m,F p.val.1 p.val.2 := by
    apply Finset.sum_congr rfl
    intro p _
    exact hF _ _
  rw [he,Fintype.sum_prod_type] at hs
  linarith

theorem upperPair_mass_le_half {m : ℕ} (F : Fin m → Fin m → ℝ)
    (hF : ∀ i j,F i j=F j i) (hdiag : ∀ i,0≤F i i) :
    (∑ p : UpperPair m,F p.val.1 p.val.2)≤(∑ i,∑ j,F i j)/2 := by
  have he := symmetric_pair_sum F hF
  have hd : 0≤∑ i,F i i := Finset.sum_nonneg (fun i _ => hdiag i)
  linarith

end APPTReview
