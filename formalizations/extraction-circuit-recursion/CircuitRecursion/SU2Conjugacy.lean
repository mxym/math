import CircuitRecursion.QuaternionPlane

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

theorem su2_inverse_conjugate (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ P : Matrix.unitaryGroup (Fin 2) ℂ,
      V.valᴴ=(P : Matrix (Fin 2) (Fin 2) ℂ)*V.val*(star P : Matrix (Fin 2) (Fin 2) ℂ) := by
  by_cases hb : V.val 0 1=0
  · let P := su2AsUnitary (quaternionSU2 0 1 (by norm_num))
    refine ⟨P,intertwiner_conjugates _ _ P ?_⟩
    change V.valᴴ*quaternionMatrix 0 1=quaternionMatrix 0 1*V.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
        su2_lower_left,su2_lower_right,hb]
  · have hq : Complex.I*V.val 0 1≠0 := mul_ne_zero Complex.I_ne_zero hb
    have hp : 0<Complex.normSq 0+Complex.normSq (Complex.I*V.val 0 1) := by
      simpa using Complex.normSq_pos.mpr hq
    let P := normalizedQuaternion 0 (Complex.I*V.val 0 1) hp
    refine ⟨P,intertwiner_conjugates _ _ P ?_⟩
    apply normalizedQuaternion_intertwines
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
        su2_lower_left,su2_lower_right] <;> ring

/-- Equality of the actual SU(2) scalar part implies conjugacy. The proof
constructs a normalized quaternion-form intertwiner and handles its zero
case explicitly, without an unproved axis-alignment certificate. -/
theorem su2_sameScalar_conjugate (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hr : (U.val 0 0).re=(V.val 0 0).re) :
    ∃ P : Matrix.unitaryGroup (Fin 2) ℂ,
      U.val=(P : Matrix (Fin 2) (Fin 2) ℂ)*V.val*(star P : Matrix (Fin 2) (Fin 2) ℂ) := by
  by_cases he : U.val=V.valᴴ
  · rw [he]
    exact su2_inverse_conjugate V
  · let a := U.val 0 0-star (V.val 0 0)
    let b := U.val 0 1+V.val 0 1
    have hp : 0<Complex.normSq a+Complex.normSq b := by
      by_contra hn
      have ha : Complex.normSq a=0 := by
        nlinarith [Complex.normSq_nonneg a,Complex.normSq_nonneg b]
      have hb : Complex.normSq b=0 := by
        nlinarith [Complex.normSq_nonneg a,Complex.normSq_nonneg b]
      have ha' : a=0 := Complex.normSq_eq_zero.mp ha
      have hb' : b=0 := Complex.normSq_eq_zero.mp hb
      have hq : quaternionMatrix a b=0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [quaternionMatrix,ha',hb']
      apply he
      apply sub_eq_zero.mp
      exact (quaternion_difference U V).trans hq
    let P := normalizedQuaternion a b hp
    refine ⟨P,intertwiner_conjugates _ _ P ?_⟩
    apply normalizedQuaternion_intertwines
    change U.val*quaternionMatrix (U.val 0 0-star (V.val 0 0)) (U.val 0 1+V.val 0 1)=
      quaternionMatrix (U.val 0 0-star (V.val 0 0)) (U.val 0 1+V.val 0 1)*V.val
    rw [← quaternion_difference]
    exact su2_intertwiner U V hr

def su2Conjugate (P : Matrix.unitaryGroup (Fin 2) ℂ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  let W := P*su2AsUnitary U*star P
  have hdetU : U.val.det=1 := U.property.2
  have hPP : (P : Matrix (Fin 2) (Fin 2) ℂ)*(star P : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Unitary.coe_mul_star_self P
  refine ⟨W.val,W.property,?_⟩
  change ((P : Matrix (Fin 2) (Fin 2) ℂ)*U.val*(star P : Matrix (Fin 2) (Fin 2) ℂ)).det=1
  rw [Matrix.det_mul,Matrix.det_mul,hdetU,mul_one,← Matrix.det_mul,hPP,Matrix.det_one]

theorem su2Conjugate_unitary (P : Matrix.unitaryGroup (Fin 2) ℂ)
    (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    su2AsUnitary (su2Conjugate P U)=P*su2AsUnitary U*star P := rfl

theorem unitaryDistance_conjugate_one (P U : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryDistance (P*U*star P) 1=unitaryDistance U 1 := by
  have hP : P*1*star P=1 := by simp
  conv_lhs => rw [← hP]
  rw [unitaryDistance_mul_right,unitaryDistance_mul_left]

end CircuitRecursion
