import CircuitCompletion.TwoLevelRotation
import CircuitCompletion.FourMerge

open scoped BigOperators
open Matrix
namespace CircuitCompletion

noncomputable def trigRotation (θ : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  rotationUnitary (Real.cos θ) (Real.sin θ) (by nlinarith [Real.sin_sq_add_cos_sq θ])

theorem rotationWord_denote {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y) (θ : ℝ) :
    denote (rotationWord hn x y h θ)=
      embedPlane (pairPlane x y h) (pairPlane_isometry x y h) (trigRotation θ) := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  change run (rotationWord hn x y h θ) v=_
  rw [rotationWord_action,embedPlane_apply,pairPlane_adjoint_mulVec]
  have htwo : (trigRotation θ : Matrix (Fin 2) (Fin 2) ℂ)*ᵥ![v x,v y]=
      ![(Real.cos θ : ℂ)*v x+(Real.sin θ : ℂ)*v y,
        -(Real.sin θ : ℂ)*v x+(Real.cos θ : ℂ)*v y] := by
    ext i
    fin_cases i <;> simp [trigRotation,rotationUnitary,rotationMatrix,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two]
  rw [htwo,pairPlane_mulVec,pairPlane_mulVec]
  funext w
  by_cases hw : w=x
  · subst w;simp [Pi.single_apply,h,Ne.symm h]
  · by_cases hwy : w=y
    · subst w;simp [Pi.single_apply,h,Ne.symm h]
    · simp [Pi.single_apply,hw,hwy,Ne.symm hw,Ne.symm hwy]

noncomputable def circleAngle (c s : ℝ) : ℝ := ((c : ℂ)+(s : ℂ)*Complex.I).arg

theorem circleAngle_trig (c s : ℝ) (h : c*c+s*s=1) :
    Real.cos (circleAngle c s)=c ∧ Real.sin (circleAngle c s)=s := by
  let z : ℂ := (c : ℂ)+(s : ℂ)*Complex.I
  have hz : Complex.normSq z=1 := by
    simpa [z,Complex.normSq_apply,pow_two] using h
  have hnorm : ‖z‖=1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hp := Complex.norm_mul_exp_arg_mul_I z
  rw [hnorm,Complex.ofReal_one,one_mul] at hp
  have he : complexPhase (circleAngle c s)=z := hp
  rw [complexPhase_trig] at he
  constructor
  · have hr := congrArg Complex.re he
    simpa only [z,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero] using hr
  · have hi := congrArg Complex.im he
    simpa only [z,Complex.add_im,Complex.ofReal_re,Complex.mul_im,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,zero_add,add_zero] using hi

noncomputable def mergeAngle (a b : ℝ) : ℝ :=
  if a+b=0 then 0 else circleAngle (Real.sqrt a/Real.sqrt (a+b))
    (Real.sqrt b/Real.sqrt (a+b))

theorem mergeRotation_eq_trig (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    mergeRotation a b ha hb=trigRotation (mergeAngle a b) := by
  by_cases h : a+b=0
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mergeRotation,h,mergeAngle,trigRotation,rotationUnitary,rotationMatrix]
  · have hp : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    have hr : Real.sqrt (a+b)≠0 := (Real.sqrt_pos.mpr hp).ne'
    have hc : (Real.sqrt a/Real.sqrt (a+b))*(Real.sqrt a/Real.sqrt (a+b))+
        (Real.sqrt b/Real.sqrt (a+b))*(Real.sqrt b/Real.sqrt (a+b))=1 := by
      field_simp
      nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hp.le]
    have ht := circleAngle_trig _ _ hc
    apply Subtype.ext
    simp only [mergeRotation,dif_neg h,mergeAngle,if_neg h,trigRotation,rotationUnitary]
    rw [ht.1,ht.2]

/-- Fully synthesized algebraic Givens word, including the zero-mass case. -/
noncomputable def mergeWord {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a b : ℝ) : Circuit n := rotationWord hn x y h (mergeAngle a b)

theorem mergeWord_denote {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    denote (mergeWord hn x y h a b)=mergeAt x y h a b ha hb := by
  rw [mergeWord,rotationWord_denote,mergeAt,mergeRotation_eq_trig]

theorem mergeWord_length {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y) (a b : ℝ) :
    (mergeWord hn x y h a b).length≤
      2*n*(2^n*(2*n+1)+2)+2*(2^n*(2*n+1))+2 :=
  rotationWord_length hn x y h _

end CircuitCompletion
