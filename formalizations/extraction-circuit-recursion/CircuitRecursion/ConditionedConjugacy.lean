import CircuitRecursion.RationalSelection

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

/-- Four fixed quaternion frames. Their conjugations flip complementary
pairs of imaginary coordinates, so one intertwiner is well conditioned. -/
def conjugacyFrame : Fin 4 → SU2 := ![
  quaternionSU2 1 0 (by norm_num),
  quaternionSU2 Complex.I 0 (by norm_num),
  quaternionSU2 0 1 (by norm_num),
  quaternionSU2 0 Complex.I (by norm_num)]

def conjugacyTarget (V : SU2) (j : Fin 4) : SU2 :=
  su2Conjugate (su2AsUnitary (conjugacyFrame j)) V

theorem conjugacyTarget_entries (V : SU2) :
    (fun j => (conjugacyTarget V j).val 0 0)=
      ![V.val 0 0,V.val 0 0,star (V.val 0 0),star (V.val 0 0)] ∧
    (fun j => (conjugacyTarget V j).val 0 1)=
      ![V.val 0 1,-V.val 0 1,star (V.val 0 1),-star (V.val 0 1)] := by
  constructor <;> funext j <;> fin_cases j <;>
    simp [conjugacyTarget,su2Conjugate,su2AsUnitary,conjugacyFrame,quaternionSU2,
      quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
      Matrix.star_eq_conjTranspose,Matrix.vecMul,Matrix.mulVec,dotProduct,
      Matrix.star_apply,su2_lower_left,su2_lower_right]
  all_goals rw [mul_left_comm Complex.I _ Complex.I]; simp

theorem conjugacyTarget_scalar (V : SU2) (j : Fin 4) :
    ((conjugacyTarget V j).val 0 0).re=(V.val 0 0).re := by
  rw [congrFun (conjugacyTarget_entries V).1 j]
  fin_cases j <;> simp

noncomputable def intertwinerMass (U V : SU2) (j : Fin 4) : ℝ :=
  Complex.normSq (U.val 0 0-star ((conjugacyTarget V j).val 0 0))+
    Complex.normSq (U.val 0 1+(conjugacyTarget V j).val 0 1)

theorem intertwinerMass_nonneg (U V : SU2) (j : Fin 4) :
    0 ≤ intertwinerMass U V j := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- A quantitative four-chart identity; no division by a potentially tiny
unselected intertwiner is required. -/
theorem intertwinerMass_sum (U V : SU2) (hr : (U.val 0 0).re=(V.val 0 0).re) :
    (∑ j,intertwinerMass U V j)=8*(1-(U.val 0 0).re^2) := by
  have hU := su2_mass U
  have hV := su2_mass V
  simp only [Complex.normSq_apply] at hU hV
  simp only [intertwinerMass,congrFun (conjugacyTarget_entries V).1,
    congrFun (conjugacyTarget_entries V).2]
  simp [Fin.sum_univ_succ,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im]
  nlinarith

theorem intertwinerMass_large (U V : SU2) (hr : (U.val 0 0).re=(V.val 0 0).re) :
    ∃ j,2*(1-(U.val 0 0).re^2) ≤ intertwinerMass U V j := by
  by_contra hn
  push_neg at hn
  have hs : (∑ j,intertwinerMass U V j)<∑ _j : Fin 4,2*(1-(U.val 0 0).re^2) :=
    Finset.sum_lt_sum_of_nonempty (by simp) (fun j hj => hn j)
  rw [intertwinerMass_sum U V hr] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num at hs
  linarith

def rationalMaxIndex (n : ℕ) (score : Fin (n+1) → ℚ) : Fin (n+1) :=
  rationalMinIndex n (fun j => -score j)

theorem rationalMaxIndex_error (n : ℕ) (score : Fin (n+1) → ℚ)
    (trueScore : Fin (n+1) → ℝ) (η : ℝ)
    (he : ∀ j,|(score j:ℝ)-trueScore j|≤η) (i : Fin (n+1)) :
    trueScore i-2*η≤trueScore (rationalMaxIndex n score) := by
  have he' : ∀ j,|((-score j:ℚ):ℝ)-(-trueScore j)|≤η := by
    intro j
    simpa only [Rat.cast_neg,neg_sub_neg,abs_sub_comm] using he j
  have ht := rationalMinIndex_error n (fun j => -score j) (fun j => -trueScore j) η he' i
  change -trueScore (rationalMaxIndex n score)≤-trueScore i+2*η at ht
  linarith

/-- A rational-score chart choice has an explicit normalization denominator
lower bound once a residual exceeds the stated stopping threshold. -/
theorem conditionedChart_denominator (U V : SU2)
    (hr : (U.val 0 0).re=(V.val 0 0).re)
    (σ η : ℝ) (hσ : 0<σ)
    (hσd : σ≤unitaryDistance (su2AsUnitary U) 1)
    (hd : unitaryDistance (su2AsUnitary U) 1≤1)
    (hη : η≤σ^2/4) (score : Fin 4 → ℚ)
    (he : ∀ j,|(score j:ℝ)-intertwinerMass U V j|≤η) :
    σ/2≤Real.sqrt (intertwinerMass U V (rationalMaxIndex 3 score)) := by
  obtain ⟨j,hj⟩ := intertwinerMass_large U V hr
  have hsel := rationalMaxIndex_error 3 score (intertwinerMass U V) η he j
  have hd0 := unitaryDistance_nonneg (su2AsUnitary U) 1
  have hd2 := su2_distance_square U
  have hscalar := su2_scalarPart_bounds U
  have hmass := intertwinerMass_nonneg U V (rationalMaxIndex 3 score)
  have hroot := Real.sq_sqrt hmass
  have hroot0 := Real.sqrt_nonneg (intertwinerMass U V (rationalMaxIndex 3 score))
  have hr0 : 0≤(U.val 0 0).re := by nlinarith
  have hmain : unitaryDistance (su2AsUnitary U) 1^2≤2*(1-(U.val 0 0).re^2) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hscalar.2)]
  nlinarith

/-- The selected formula uses one normalized quaternion followed by one of
the four fixed frames. Its denominator is the previously bounded mass. -/
noncomputable def chartConjugator (U V : SU2) (j : Fin 4)
    (hp : 0 < intertwinerMass U V j) : Matrix.unitaryGroup (Fin 2) ℂ :=
  normalizedQuaternion (U.val 0 0-star ((conjugacyTarget V j).val 0 0))
    (U.val 0 1+(conjugacyTarget V j).val 0 1) hp * su2AsUnitary (conjugacyFrame j)

theorem chartConjugator_action (U V : SU2) (j : Fin 4)
    (hr : (U.val 0 0).re=(V.val 0 0).re) (hp : 0 < intertwinerMass U V j) :
    su2AsUnitary U=chartConjugator U V j hp*su2AsUnitary V*star (chartConjugator U V j hp) := by
  let W := conjugacyTarget V j
  let P := normalizedQuaternion (U.val 0 0-star (W.val 0 0)) (U.val 0 1+W.val 0 1) hp
  let S := su2AsUnitary (conjugacyFrame j)
  have hscalar : (U.val 0 0).re=(W.val 0 0).re := hr.trans (conjugacyTarget_scalar V j).symm
  have hinter : U.val*(P : Matrix (Fin 2) (Fin 2) ℂ)=(P : Matrix (Fin 2) (Fin 2) ℂ)*W.val := by
    apply normalizedQuaternion_intertwines
    rw [← quaternion_difference]
    exact su2_intertwiner U W hscalar
  have hact : su2AsUnitary U=P*su2AsUnitary W*star P := by
    apply Subtype.ext
    exact intertwiner_conjugates U.val W.val P hinter
  calc
    su2AsUnitary U=P*su2AsUnitary W*star P := hact
    _=P*(S*su2AsUnitary V*star S)*star P := rfl
    _=(P*S)*su2AsUnitary V*star (P*S) := by simp only [star_mul,mul_assoc]

end CircuitRecursion
