import RationalGateUniversality.Tori

open CircuitRecursion Matrix
open scoped ComplexConjugate
namespace RationalGateUniversality

set_option maxHeartbeats 1000000

theorem z_x_z_entry00 (s t r : Circle) :
    (zTorus s * xTorus t * zTorus r).val 0 0 =
      ((t : ℂ).re : ℂ) * ((s*r : Circle) : ℂ) := by
  simp [zTorus, xTorus, quaternionSU2, quaternionMatrix]
  ring

theorem z_x_z_entry01 (s t r : Circle) :
    (zTorus s * xTorus t * zTorus r).val 0 1 =
      Complex.I * ((t : ℂ).im : ℂ) * ((s*r⁻¹ : Circle) : ℂ) := by
  rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp [zTorus, xTorus, quaternionSU2, quaternionMatrix]
  ring

/-- Full ZXZ factorization. The polar identity used here is valid at zero;
no division by an entry and no continuity of a chosen phase is needed. -/
theorem su2_euler (U : SU2) : ∃ s t r : Circle, U = zTorus s * xTorus t * zTorus r := by
  let a := U.val 0 0
  let b := U.val 0 1
  have hm : ‖a‖^2 + ‖b‖^2 = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using su2_mass U
  have ht : ‖(⟨‖a‖, ‖b‖⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) = 1
    rw [← pow_two, ← pow_two, hm, Real.sqrt_one]
  let t : Circle := ⟨⟨‖a‖, ‖b‖⟩, by simpa [Submonoid.unitSphere] using ht⟩
  let α := Complex.arg a
  let β := Complex.arg (-Complex.I*b)
  let s := Circle.exp ((α+β)/2)
  let r := Circle.exp ((α-β)/2)
  have hsr : s*r = Circle.exp α := by
    dsimp only [s, r]
    rw [← Circle.exp_add]
    congr 1
    ring
  have hsri : s*r⁻¹ = Circle.exp β := by
    dsimp only [s, r]
    rw [← Circle.exp_neg, ← Circle.exp_add]
    congr 1
    ring
  refine ⟨s,t,r, (ext_first_row (zTorus s*xTorus t*zTorus r) U ?_ ?_).symm⟩
  · rw [z_x_z_entry00, hsr]
    change (‖a‖ : ℂ) * (Circle.exp α : ℂ) = a
    exact Complex.norm_mul_exp_arg_mul_I a
  · rw [z_x_z_entry01, hsri]
    change Complex.I * (‖b‖ : ℂ) * (Circle.exp β : ℂ) = b
    have hb : (‖b‖ : ℂ) * (Circle.exp β : ℂ) = -Complex.I*b := by
      simpa [β, Circle.coe_exp, norm_mul] using
        Complex.norm_mul_exp_arg_mul_I (-Complex.I*b)
    calc
      _ = Complex.I * ((‖b‖ : ℂ) * (Circle.exp β : ℂ)) := by ring
      _ = Complex.I * (-Complex.I*b) := by rw [hb]
      _ = b := by simp [← mul_assoc]

end RationalGateUniversality
