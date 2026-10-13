import APPTReview.LacunaryFiniteGraph

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview

/-- A weight cap is essential to the fractional Cauchy estimate. -/
theorem fractional_cap_cannot_be_dropped : ¬(4:ℝ)≤Real.sqrt (4*(1:ℝ)^2) := by
  norm_num

/-- Coincident atoms and a zero weight still give one full unit of actual
probability mass. They are not counted as distinct graph vertices by the measure. -/
theorem atomic_zero_and_collision_control :
    let p : Fin 2 → ℝ := fun i => if i=0 then 1 else 0
    let x : Fin 2 → ℝ≥0 := fun _ => 1
    IsProbabilityMeasure (finiteAtomicMeasure p x) ∧
      ((finiteAtomicMeasure p x).prod (finiteAtomicMeasure p x)).real (scaleBand 2 0)=1 := by
  classical
  dsimp only
  let p : Fin 2 → ℝ := fun i => if i=0 then 1 else 0
  let x : Fin 2 → ℝ≥0 := fun _ => 1
  have hp : ∀ i,0≤p i := by intro i;dsimp [p];split_ifs <;> norm_num
  have hs : (∑ i,p i)=1 := by norm_num [p,Fin.sum_univ_two]
  refine ⟨finiteAtomicMeasure_probability p x hp hs,?_⟩
  rw [finiteAtomicMeasure_prod p p x x hp hp,
    finiteAtomicMeasure_real (fun z : Fin 2×Fin 2 => p z.1*p z.2)
      (fun z : Fin 2×Fin 2 => (x z.1,x z.2)) (fun z => mul_nonneg (hp z.1) (hp z.2))]
  norm_num [p,x,Fintype.sum_prod_type,Fin.sum_univ_two,scaleBand]

end APPTReview
