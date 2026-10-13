import APPTReview.SparseMatrixBound

open scoped BigOperators
open Matrix
namespace APPTReview

/-- The weight-at-most-one condition is essential to the Cauchy budget. -/
theorem fractional_weight_cap_cannot_be_dropped :
    ¬((2:ℝ)≤Real.sqrt (2*1)) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2*1)
  have hn := Real.sqrt_nonneg (2*1:ℝ)
  intro h
  nlinarith

/-- Small but nonzero products cannot be erased by keeping only the band. -/
theorem outside_band_mass_not_zero :
    (∑ i : Fin 1,(1:ℝ)*(1/4))=1/4 ∧
    (∑ i∈(Finset.univ : Finset (Fin 1)).filter
      (fun _ => (1/2:ℝ)≤1/4 ∧ (1/4:ℝ)≤1),(1/4:ℝ)^2)=0 := by
  norm_num

/-- Either endpoint can be bad: a one-ended error is insufficient. -/
theorem bad_pair_factor_cannot_be_one :
    let p : Fin 2 → ℝ := ![1/4,3/4]
    let G : Finset (Fin 2) := {1}
    (∑ z : Fin 2 × Fin 2,if z.1∈G ∧ z.2∈G then 0 else p z.1*p z.2)=7/16 ∧
    (∑ i : Fin 2,if i∈G then 0 else p i)=1/4 ∧ (1/4:ℝ)<7/16 := by
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two]

/-- Clipping the two logarithmic positions can enlarge the band beyond 2 eta. -/
theorem clipping_band_factor_cannot_be_two :
    |amplitudeScale 1 (Real.exp (-11/20))+amplitudeScale 1 (Real.exp (-9/40))-(1/4:ℝ)|=3/10 ∧
    2*(1/10:ℝ)<3/10 := by
  norm_num [amplitudeScale,rawAmplitudeScale,Real.log_exp]

theorem zero_amplitude_scale_defined : amplitudeScale 1 0=1 := by
  norm_num [amplitudeScale,rawAmplitudeScale]

/-- Without symmetry a Rayleigh cap does not bound the Euclidean operator norm. -/
theorem nonsymmetric_rayleigh_not_operator_cap :
    let A : Matrix (Fin 2) (Fin 2) ℝ := ![![0,2],![0,0]]
    (∀ s : Fin 2 → ℝ,(∑ i,(s i)^2)=1 → realRayleigh A s≤1) ∧
    (∑ i : Fin 2,(A*ᵥ(![0,1]:Fin 2 → ℝ)) i^2)=4 := by
  dsimp only
  constructor
  · intro s hs
    norm_num [realRayleigh,Fintype.sum_prod_type,Fin.sum_univ_two] at hs ⊢
    nlinarith [sq_nonneg (s 0-s 1)]
  · norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two]

end APPTReview
