import GaussianAllCellsFlux
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Algebraic consequence of a genuine triple-junction force balance.
The balance itself remains a geometric obligation; it is not assumed as a
property of arbitrary winning clusters. -/
open Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {e k : ℕ}

theorem triple_unit_normal_balance_lengths
    (v : Fin k → Space e) (hv : AffineIndependent ℝ v)
    (i j l : Fin k) (hij : i ≠ j) (hjl : j ≠ l) (hli : l ≠ i)
    (hbalance : ‖v i-v j‖⁻¹ • (v i-v j)+
      ‖v j-v l‖⁻¹ • (v j-v l)+‖v l-v i‖⁻¹ • (v l-v i) = 0) :
    ‖v i-v j‖ = ‖v j-v l‖ ∧ ‖v j-v l‖ = ‖v l-v i‖ := by
  classical
  let f : Fin 2 → {a : Fin k // a ≠ i} := ![⟨j,Ne.symm hij⟩,⟨l,hli⟩]
  have hf : Function.Injective f := by
    intro a b he
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hjl (congrArg Subtype.val he)).elim
    · exact (hjl (congrArg Subtype.val he).symm).elim
    · rfl
  have hp := (((affineIndependent_iff_linearIndependent_vsub ℝ v i).mp hv).comp f hf).neg
  have hpair : LinearIndependent ℝ ![v i-v j,v i-v l] := by
    convert hp using 1
    funext a
    fin_cases a <;> simp [f]
  have hsub : v j-v l = (v i-v l)-(v i-v j) := by abel
  have hneg : v l-v i = -(v i-v l) := by abel
  have hrel : (‖v i-v j‖⁻¹-‖v j-v l‖⁻¹) • (v i-v j)+
      (‖v j-v l‖⁻¹-‖v l-v i‖⁻¹) • (v i-v l) = 0 := by
    let a := ‖v i-v j‖⁻¹
    let b := ‖v j-v l‖⁻¹
    let c := ‖v l-v i‖⁻¹
    have hb : a • (v i-v j)+b • (v j-v l)+c • (v l-v i) = 0 := hbalance
    rw [hsub,hneg,smul_sub,smul_neg] at hb
    change (a-b) • (v i-v j)+(b-c) • (v i-v l) = 0
    convert hb using 1 <;> module
  obtain ⟨ha,hc⟩ := hpair.eq_zero_of_pair hrel
  exact ⟨inv_injective (sub_eq_zero.mp ha),inv_injective (sub_eq_zero.mp hc)⟩

end GaussianMeasureBridge
