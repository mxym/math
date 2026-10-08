import BapatMovingCloud
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

abbrev RealSpace4 := EuclideanSpace ℝ (Fin 4)
abbrev Orthogonal4 := unitary (RealSpace4 →L[ℝ] RealSpace4)

instance realOperator4_continuousStar : ContinuousStar (RealSpace4 →L[ℝ] RealSpace4) where
  continuous_star := ContinuousLinearMap.adjoint.continuous

instance orthogonal4_compactSpace : CompactSpace Orthogonal4 := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_sphere (0 : RealSpace4 →L[ℝ] RealSpace4) 1).of_isClosed_subset isClosed_unitary
  intro x hx
  simpa only [mem_sphere_zero_iff_norm] using CStarRing.norm_of_mem_unitary hx

instance orthogonal4_measurableSpace : MeasurableSpace Orthogonal4 := borel Orthogonal4
instance orthogonal4_borelSpace : BorelSpace Orthogonal4 := ⟨rfl⟩

def orthogonalSphereAction (R : Orthogonal4) : RealUnitSphere4 ≃ₜ RealUnitSphere4 :=
  unitSphereHomeomorph (Unitary.linearIsometryEquiv R)

@[fun_prop] theorem orthogonalSphereAction_continuous :
    Continuous (fun p : Orthogonal4 × RealUnitSphere4 => orthogonalSphereAction p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Orthogonal4 × RealUnitSphere4 =>
    ((p.1 : RealSpace4 →L[ℝ] RealSpace4) : RealSpace4 → RealSpace4) (p.2 : RealSpace4))
  fun_prop

theorem orthogonalSphereAction_measurePreserving (R : Orthogonal4) :
    MeasurePreserving (orthogonalSphereAction R)
      (normalizedSphere (volume : Measure RealSpace4))
      (normalizedSphere (volume : Measure RealSpace4)) :=
  measurePreserving_normalizedSphere _

/-- Arbitrarily changing real orthogonal coordinates preserve the actual cloud's
limiting uniform measure, without a continuous choice of coordinate changes. -/
theorem moving_orthogonal_cloud (u : ℕ → RealUnitSphere4)
    (hu : ∀ f : C(RealUnitSphere4, ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (R : ℕ → Orthogonal4) (f : C(RealUnitSphere4, ℝ)) :
    Tendsto (fun n => empiricalAverage u n (fun x => f (orthogonalSphereAction (R n) x))) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))) :=
  moving_measurePreserving_cloud _ u hu (fun R x => orthogonalSphereAction R x)
    orthogonalSphereAction_continuous orthogonalSphereAction_measurePreserving R f

theorem orthogonalSphereAction_transitive (u v : RealUnitSphere4) :
    ∃ R : Orthogonal4, orthogonalSphereAction R u = v := by
  let e := (Submodule.span ℝ {(u : RealSpace4) - (v : RealSpace4)})ᗮ.reflection
  have he : e (u : RealSpace4) = v :=
    Submodule.reflection_sub (by simpa using u.property.trans v.property.symm)
  refine ⟨Unitary.linearIsometryEquiv.symm e, ?_⟩
  apply Subtype.ext
  exact he

/-- Probability Haar measure normalized on the whole compact orthogonal group. -/
def orthogonalLeftHaar : Measure Orthogonal4 := Measure.haarMeasure ⊤

instance orthogonalLeftHaar_isProbability : IsProbabilityMeasure orthogonalLeftHaar where
  measure_univ := Measure.haarMeasure_self (K₀ := ⊤)

instance orthogonalLeftHaar_isHaar : IsHaarMeasure orthogonalLeftHaar :=
  Measure.isHaarMeasure_haarMeasure _

/-- Right Haar probability is convenient for orbit averages under a left action. -/
def orthogonalHaar : Measure Orthogonal4 := orthogonalLeftHaar.inv

instance orthogonalHaar_isProbability : IsProbabilityMeasure orthogonalHaar where
  measure_univ := by simp [orthogonalHaar, Measure.inv_apply]

instance orthogonalHaar_isMulRightInvariant : IsMulRightInvariant orthogonalHaar :=
  Measure.inv.instIsMulRightInvariant

@[simp] theorem orthogonalSphereAction_mul (R S : Orthogonal4) (u : RealUnitSphere4) :
    orthogonalSphereAction (R*S) u = orthogonalSphereAction R (orthogonalSphereAction S u) := by
  apply Subtype.ext
  rfl

theorem orthogonal_orbit_integral (u : RealUnitSphere4) (f : RealUnitSphere4 → ℝ)
    (hf : Continuous f) :
    (∫ R, f (orthogonalSphereAction R u) ∂orthogonalHaar) =
      ∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4) := by
  let σ := normalizedSphere (volume : Measure RealSpace4)
  have hconstant (x : RealUnitSphere4) :
      (∫ R, f (orthogonalSphereAction R x) ∂orthogonalHaar) =
        ∫ R, f (orthogonalSphereAction R u) ∂orthogonalHaar := by
    obtain ⟨S, hS⟩ := orthogonalSphereAction_transitive u x
    rw [← hS]
    simp_rw [← orthogonalSphereAction_mul]
    exact integral_mul_right_eq_self (fun R => f (orthogonalSphereAction R u)) S
  have hi : Integrable (fun p : RealUnitSphere4 × Orthogonal4 =>
      f (orthogonalSphereAction p.2 p.1)) (σ.prod orthogonalHaar) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hf.comp (orthogonalSphereAction_continuous.comp continuous_swap)
  calc
    _ = ∫ x, ∫ R, f (orthogonalSphereAction R x) ∂orthogonalHaar ∂σ := by
      simp_rw [hconstant]
      simp
    _ = ∫ R, ∫ x, f (orthogonalSphereAction R x) ∂σ ∂orthogonalHaar :=
      integral_integral_swap hi
    _ = ∫ R, ∫ x, f x ∂σ ∂orthogonalHaar := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro R
      exact (orthogonalSphereAction_measurePreserving R).integral_comp
        (orthogonalSphereAction R).measurableEmbedding f
    _ = _ := by simp [σ]

/-- A rotated fixed unit real vector has exactly normalized sphere law. -/
theorem orthogonal_orbit_map (u : RealUnitSphere4) :
    Measure.map (fun R => orthogonalSphereAction R u) orthogonalHaar =
      normalizedSphere (volume : Measure RealSpace4) := by
  have hc : Continuous (fun R => orthogonalSphereAction R u) :=
    orthogonalSphereAction_continuous.comp (continuous_id.prodMk continuous_const)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact orthogonal_orbit_integral u f f.continuous

end
end BapatRealExistence
