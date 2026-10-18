import CircuitRecursion.SpecialUnitaryNet

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

def su2AsUnitary (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix.unitaryGroup (Fin 2) ℂ := ⟨U.val,U.property.1⟩

theorem su2_adjugate (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix.adjugate U.val=U.valᴴ := by
  have hmul := Matrix.mul_adjugate U.val
  have hdet : U.val.det=1 := U.property.2
  rw [hdet,one_smul] at hmul
  have hstar : U.valᴴ*U.val=1 := U.property.1.1
  calc
    Matrix.adjugate U.val=1*Matrix.adjugate U.val := by rw [one_mul]
    _ = (U.valᴴ*U.val)*Matrix.adjugate U.val := by rw [hstar]
    _ = U.valᴴ*(U.val*Matrix.adjugate U.val) := mul_assoc _ _ _
    _ = U.valᴴ := by rw [hmul,mul_one]

theorem su2_lower_left (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val 1 0=-star (U.val 0 1) := by
  have h := congrArg star (congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) (su2_adjugate U))
  simpa [Matrix.adjugate_fin_two,Matrix.conjTranspose_apply] using h.symm

theorem su2_lower_right (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val 1 1=star (U.val 0 0) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) (su2_adjugate U)
  simpa [Matrix.adjugate_fin_two,Matrix.conjTranspose_apply] using h

theorem su2_normalForm (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val=!![U.val 0 0,U.val 0 1;-star (U.val 0 1),star (U.val 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2_lower_left,su2_lower_right]

theorem su2_mass (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Complex.normSq (U.val 0 0)+Complex.normSq (U.val 0 1)=1 := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).re) U.property.1.2
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,Matrix.one_apply,
    if_true,Complex.one_re,Complex.add_re] at h
  simpa [Complex.normSq_apply,Complex.mul_re] using h

theorem su2_scalarPart_bounds (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    -1≤(U.val 0 0).re ∧ (U.val 0 0).re≤1 := by
  have hm := su2_mass U
  rw [Complex.normSq_apply,Complex.normSq_apply] at hm
  constructor <;> nlinarith [sq_nonneg (U.val 0 0).im,
    sq_nonneg (U.val 0 1).re,sq_nonneg (U.val 0 1).im]

theorem su2_trace (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val.trace=((2*(U.val 0 0).re : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two]
  rw [su2_lower_right]
  exact Complex.add_conj _

theorem su2_add_adjoint (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U.val+U.valᴴ=(2*(U.val 0 0).re : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply,su2_lower_left,su2_lower_right]
  · simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.add_conj (U.val 0 0)
  · simpa only [add_comm,Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.add_conj (U.val 0 0)

theorem su2_distance_square (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    unitaryDistance (su2AsUnitary U) 1^2=2-2*(U.val 0 0).re := by
  have hstar : U.valᴴ*U.val=1 := U.property.1.1
  have hs : (U.val-1)ᴴ*(U.val-1)=
      (2-2*(U.val 0 0).re : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have he : (U.val-1)ᴴ*(U.val-1)=(2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)-(U.val+U.valᴴ) := by
      simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.sub_mul,
        Matrix.mul_sub,hstar,Matrix.one_mul,Matrix.mul_one]
      module
    rw [he,su2_add_adjoint,← sub_smul]
  have hpos : 0≤2-2*(U.val 0 0).re := by
    have hb := (su2_scalarPart_bounds U).2
    linarith
  have hn := CStarRing.norm_star_mul_self (x := U.val-1)
  change ‖(U.val-1)ᴴ*(U.val-1)‖=‖U.val-1‖*‖U.val-1‖ at hn
  rw [hs,norm_smul,norm_one,Real.norm_eq_abs,abs_of_nonneg hpos,mul_one] at hn
  simpa [unitaryDistance,su2AsUnitary,pow_two] using hn.symm

end CircuitRecursion
