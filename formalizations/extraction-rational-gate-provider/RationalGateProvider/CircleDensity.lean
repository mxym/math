import RationalGateProvider.GaussianAngle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace RationalGateProvider

noncomputable def phaseCircle : Circle :=
  ⟨rationalPhase, by
    simp [Submonoid.unitSphere, Complex.norm_def, rationalPhase_normSq]⟩

theorem phaseCircle_pow_ne_one (n : ℕ) (hn : 0 < n) : phaseCircle ^ n ≠ 1 := by
  intro h
  apply rationalPhase_pow_ne_one n hn
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  rw [Circle.coe_pow, Circle.coe_one] at hc
  exact hc

noncomputable def phaseAngle : AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm phaseCircle

theorem phaseAngle_image : AddCircle.toCircle phaseAngle = phaseCircle := by
  rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
  exact (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).apply_symm_apply _

theorem phaseAngle_infinite_order : addOrderOf phaseAngle = 0 := by
  by_contra hn
  have hp : 0 < addOrderOf phaseAngle := Nat.pos_of_ne_zero hn
  have hz := addOrderOf_nsmul_eq_zero phaseAngle
  have hc := congrArg (@AddCircle.toCircle (1 : ℝ)) hz
  rw [AddCircle.toCircle_nsmul, AddCircle.toCircle_zero, phaseAngle_image] at hc
  exact phaseCircle_pow_ne_one _ hp hc

theorem phaseCircle_dense_zpowers : DenseRange (fun n : ℤ => phaseCircle ^ n) := by
  have : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hd : DenseRange (fun n : ℤ => n • phaseAngle) :=
    AddCircle.denseRange_zsmul_iff.mpr phaseAngle_infinite_order
  let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  have he := e.surjective.denseRange.comp hd e.continuous
  have same : e ∘ (fun n : ℤ => n • phaseAngle) = (fun n : ℤ => phaseCircle ^ n) := by
    funext n
    simp only [Function.comp_apply, e, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_zsmul, phaseAngle_image]
  rwa [same] at he

end RationalGateProvider
