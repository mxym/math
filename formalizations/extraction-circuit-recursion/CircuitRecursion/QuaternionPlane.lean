import CircuitRecursion.SU2Coordinates

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

def quaternionMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a,b;-star b,star a]

theorem quaternionMatrix_star_mul (a b : ℂ) :
    (quaternionMatrix a b)ᴴ*quaternionMatrix a b=
      (Complex.normSq a+Complex.normSq b : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionMatrix,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
      Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem quaternionMatrix_det (a b : ℂ) :
    (quaternionMatrix a b).det=((Complex.normSq a+Complex.normSq b : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [quaternionMatrix,Matrix.det_fin_two,Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

def quaternionSU2 (a b : ℂ) (h : Complex.normSq a+Complex.normSq b=1) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨quaternionMatrix a b,Matrix.mem_unitaryGroup_iff'.mpr (by
    change (quaternionMatrix a b)ᴴ*quaternionMatrix a b=1
    rw [quaternionMatrix_star_mul,h,one_smul]),by
      change (quaternionMatrix a b).det=1
      rw [quaternionMatrix_det,h,Complex.ofReal_one]⟩

noncomputable def normalizedQuaternion (a b : ℂ)
    (hp : 0<Complex.normSq a+Complex.normSq b) : Matrix.unitaryGroup (Fin 2) ℂ := by
  let r := Real.sqrt (Complex.normSq a+Complex.normSq b)
  have hr : r≠0 := (Real.sqrt_pos.mpr hp).ne'
  have hs : r*r=Complex.normSq a+Complex.normSq b := Real.mul_self_sqrt hp.le
  have he : r⁻¹*r⁻¹*(Complex.normSq a+Complex.normSq b)=1 := by
    rw [← hs]
    field_simp
  refine ⟨r⁻¹ • quaternionMatrix a b,Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (r⁻¹ • quaternionMatrix a b)ᴴ*(r⁻¹ • quaternionMatrix a b)=1
  simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,quaternionMatrix_star_mul,← mul_assoc,he,one_smul]

theorem normalizedQuaternion_val (a b : ℂ)
    (hp : 0<Complex.normSq a+Complex.normSq b) :
    (normalizedQuaternion a b hp : Matrix (Fin 2) (Fin 2) ℂ)=
      (Real.sqrt (Complex.normSq a+Complex.normSq b))⁻¹ • quaternionMatrix a b := rfl

theorem normalizedQuaternion_intertwines (a b : ℂ)
    (hp : 0<Complex.normSq a+Complex.normSq b)
    (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (h : U*quaternionMatrix a b=quaternionMatrix a b*V) :
    U*(normalizedQuaternion a b hp : Matrix (Fin 2) (Fin 2) ℂ)=
      (normalizedQuaternion a b hp : Matrix (Fin 2) (Fin 2) ℂ)*V := by
  rw [normalizedQuaternion_val,Matrix.mul_smul,Matrix.smul_mul,h]

theorem quaternion_difference (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val-V.valᴴ=quaternionMatrix (U.val 0 0-star (V.val 0 0)) (U.val 0 1+V.val 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix,Matrix.conjTranspose_apply,su2_lower_left,su2_lower_right] <;> ring

theorem su2_intertwiner (U V : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hr : (U.val 0 0).re=(V.val 0 0).re) :
    U.val*(U.val-V.valᴴ)=(U.val-V.valᴴ)*V.val := by
  have hu : U.valᴴ*U.val=1 := U.property.1.1
  have hv : V.valᴴ*V.val=1 := V.property.1.1
  have he : U.val*(V.val+V.valᴴ)=(U.val+U.valᴴ)*U.val := by
    rw [su2_add_adjoint,su2_add_adjoint,hr]
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul]
  have ht : U.val*V.val+U.val*V.valᴴ=U.val*U.val+1 := by
    simpa only [Matrix.mul_add,Matrix.add_mul,hu] using he
  rw [Matrix.mul_sub,Matrix.sub_mul,hv]
  exact sub_eq_sub_iff_add_eq_add.mpr ht.symm

theorem intertwiner_conjugates (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (P : Matrix.unitaryGroup (Fin 2) ℂ)
    (hp : U*(P : Matrix (Fin 2) (Fin 2) ℂ)=(P : Matrix (Fin 2) (Fin 2) ℂ)*V) :
    U=(P : Matrix (Fin 2) (Fin 2) ℂ)*V*(star P : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hPP : (P : Matrix (Fin 2) (Fin 2) ℂ)*(star P : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Unitary.coe_mul_star_self P
  rw [← hp,Matrix.mul_assoc,hPP,Matrix.mul_one]

end CircuitRecursion
