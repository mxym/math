import APPTReview.SchmidtEmpirical

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview

/-- One weighted sparse layer is controlled by the actual common empirical
scale measure, plus explicit exponentially small errors. -/
theorem schmidt_level_localization {m : ℕ} (s : Fin m → ℝ)
    (hn : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1)
    (L : ℝ) (hL : 0<L) (hM : Real.exp L=(m:ℝ)) (d η : ℝ) (hη : 0≤η)
    (w : UpperPair m → ℝ) (hw : ∀ q,0≤w q) (hw1 : ∀ q,w q≤1)
    (hrank : (∑ q,w q)≤Real.exp ((2-d)*L)) :
    Real.exp ((d/2-1)*L)*(∑ q,w q*(s q.val.1*s q.val.2)) ≤
      2*Real.exp (-η*L)+Real.sqrt (Real.exp (-η*L))+
      Real.sqrt (((scaleLift (schmidtEmpirical s hn hs L hL)).prod
        (scaleLift (schmidtEmpirical s hn hs L hL))).toMeasure.real (scaleBand d (4*η))/2) := by
  classical
  let x := schmidtCoordinates s hn hs L hL
  let μ := scaleLift (schmidtEmpirical s hn hs L hL)
  let a := Real.exp ((d/2-1-η)*L)
  let b := Real.exp ((d/2-1+η)*L)
  let r := Real.exp ((2-d)*L)
  let c := Real.exp ((d/2-1)*L)
  let B := Real.exp (-η*L)
  let Q := (μ.prod μ).toMeasure.real (scaleBand d (4*η))/2
  let y : UpperPair m → ℝ := fun q => s q.val.1*s q.val.2
  let C : Fin m → Fin m → Prop := fun i j => a≤s i*s j ∧ s i*s j≤b
  let bad : Fin m → Prop := fun i => s i<Real.exp (-(1+η)*L/2)
  have hcover (i j : Fin m) (hij : C i j) :
      |((x i).val:ℝ)+((x j).val:ℝ)-d|≤4*η ∨ bad i ∨ bad j := by
    by_cases hi : bad i
    · exact Or.inr (Or.inl hi)
    by_cases hj : bad j
    · exact Or.inr (Or.inr hj)
    apply Or.inl
    exact schmidt_pair_in_scaleBand L d η (s i) (s j) hL hη (hn i) (hn j)
      (unit_schmidt_entry_le_one s hn hs i) (unit_schmidt_entry_le_one s hn hs j)
      (le_of_not_gt hi) (le_of_not_gt hj) hij.1 hij.2
  have hmass := selected_pair_mass_bound (fun i => (s i)^2) x
    (fun i => sq_nonneg _) hs C bad d (4*η) hcover
  have hsmall := small_schmidt_mass s hn L η hM
  let K := ∑ q∈Finset.univ.filter (fun q => a≤y q ∧ y q≤b),(y q)^2
  have hmid : K≤Q+B := by
    have he : K=(∑ q : UpperPair m,if C q.val.1 q.val.2 then (s q.val.1)^2*(s q.val.2)^2 else 0) := by
      dsimp [K]
      rw [Finset.sum_filter]
      simp only [C,y,mul_pow]
    rw [he]
    change _≤Q+(∑ i,if bad i then (s i)^2 else 0) at hmass
    change (∑ i,if bad i then (s i)^2 else 0)≤B at hsmall
    linarith
  have hr : 0<r := Real.exp_pos _
  have hc : 0<c := Real.exp_pos _
  have ha : 0<a := Real.exp_pos _
  have hb : 0<b := Real.exp_pos _
  have hB : 0≤B := (Real.exp_pos _).le
  have hQ : 0≤Q := div_nonneg measureReal_nonneg (by norm_num)
  have hab : a≤b := Real.exp_le_exp.mpr (by nlinarith)
  have hT : (∑ q,(y q)^2)≤(1:ℝ) := (schmidt_pair_square_mass s hs).trans (by norm_num)
  have hloc := fractional_strip_localization Finset.univ w y r 1 a b
    (fun q _ => hw q) (fun q _ => hw1 q)
    (fun q _ => mul_nonneg (hn q.val.1) (hn q.val.2)) hrank hT ha.le hb hab
  have hcr : c^2*r=1 := by
    dsimp [c,r]
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hcs : c*Real.sqrt r=1 := by
    have he : (c*Real.sqrt r)^2=1 := by rw [mul_pow,Real.sq_sqrt hr.le];exact hcr
    nlinarith [mul_nonneg hc.le (Real.sqrt_nonneg r)]
  have hcar : c*a*r=B := by
    dsimp [c,a,r,B]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have hcb : c/b=B := by
    dsimp [c,b,B]
    rw [← Real.exp_sub]
    congr 1
    ring
  have hroot : c*Real.sqrt (r*K)≤Real.sqrt Q+Real.sqrt B := by
    calc
      _ ≤ c*Real.sqrt (r*(Q+B)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmid hr.le)) hc.le
      _ = Real.sqrt (Q+B) := by rw [Real.sqrt_mul hr.le,← mul_assoc,hcs,one_mul]
      _ ≤ _ := sqrt_sum_le_sum_sqrt Q B hQ hB
  have hh := mul_le_mul_of_nonneg_left hloc hc.le
  have he : c*(a*r+1/b+Real.sqrt (r*K))=c*a*r+c/b+c*Real.sqrt (r*K) := by ring
  change c*(∑ q,w q*y q)≤c*(a*r+1/b+Real.sqrt (r*K)) at hh
  rw [he,hcar,hcb] at hh
  change c*(∑ q,w q*y q)≤2*B+Real.sqrt B+Real.sqrt Q
  linarith

end APPTReview
