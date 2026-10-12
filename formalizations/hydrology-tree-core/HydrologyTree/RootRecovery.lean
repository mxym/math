import HydrologyTree.PathPolynomial
import HydrologyTree.PhysicalConstants

/-! Algebraic recovery from actual characteristic/cofactor coefficients.
No local-inverse theorem or unproved generic identifiability premise is used. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

/-- Equality of the retained coefficients is exactly equality of both actual
unreduced monic polynomials. -/
theorem physicalCoefficientMap_eq_iff {n : ℕ} (t : OrderedTree n) (x y : TreeRates n) :
    physicalCoefficientMap t x = physicalCoefficientMap t y ↔
      physicalCharacteristic t x = physicalCharacteristic t y ∧
      physicalRootCofactor t x = physicalRootCofactor t y := by
  constructor
  · intro h
    constructor
    · have hp := congrArg (fun z : Coeff (n+1) × Coeff n => (monicPoly z.1 : ℝ[X])) h
      rwa [physicalCoefficientMap_first_reconstruct, physicalCoefficientMap_first_reconstruct] at hp
    · have hf := congrArg (fun z : Coeff (n+1) × Coeff n => (monicPoly z.2 : ℝ[X])) h
      rwa [physicalCoefficientMap_second_reconstruct, physicalCoefficientMap_second_reconstruct] at hf
  · rintro ⟨hp,hf⟩
    simp only [physicalCoefficientMap, hp, hf]

/-- Nonzero inward rates can be detected from an actual cofactor coefficient. -/
theorem physical_inward_nonzero_iff {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (∀ e : Fin n, x.1 e.succ ≠ 0) ↔ (physicalRootCofactor t x).eval 0 ≠ 0 := by
  rw [physicalRootCofactor_eval_zero, Finset.prod_ne_zero_iff]
  simp

/-- Any model sharing complete coefficient data with a nonzero-inward model
has the same root leak, even when the alternative model was not assumed regular. -/
theorem physical_root_leak_identified {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : ∀ e : Fin n, x.1 e.succ ≠ 0)
    (h : physicalCoefficientMap t x = physicalCoefficientMap t y) : x.1 0 = y.1 0 := by
  obtain ⟨hp,hf⟩ := (physicalCoefficientMap_eq_iff t x y).mp h
  have hy : ∀ e : Fin n, y.1 e.succ ≠ 0 := by
    apply (physical_inward_nonzero_iff t y).mpr
    rw [← hf]
    exact (physical_inward_nonzero_iff t x).mp hx
  rw [physical_root_leak_eq_ratio t x hx, physical_root_leak_eq_ratio t y hy, hp, hf]

section Transition
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complete triangular recovery, including the dimension-zero numerator case. -/
theorem rootTransition_fiber_unique (α β : P →L[ℝ] ℝ) (L K : P →L[ℝ] E)
    (z w : RootTransitionSpace P E)
    (hz : z.2.1.2 ≠ 0 ∨ Subsingleton E)
    (h : rootTransition α β L K z = rootTransition α β L K w) : z = w := by
  have hp := congrArg (fun u : RootTransitionSpace P E => u.1) h
  change z.1 = w.1 at hp
  have hd0 := congrArg (fun u : RootTransitionSpace P E => u.2.1.1) h
  change z.2.1.1 + α z.1 = w.2.1.1 + α w.1 at hd0
  rw [hp] at hd0
  have hd : z.2.1.1 = w.2.1.1 := add_right_cancel hd0
  have hc0 := congrArg (fun u : RootTransitionSpace P E => u.2.1.2) h
  change β z.1 + z.2.1.1 * α z.1 - z.2.1.2 =
    β w.1 + w.2.1.1 * α w.1 - w.2.1.2 at hc0
  rw [hp,hd] at hc0
  have hc : z.2.1.2 = w.2.1.2 := sub_right_inj.mp hc0
  have hq : z.2.2 = w.2.2 := by
    rcases hz with hz | hs
    · have hw : w.2.1.2 ≠ 0 := by rwa [← hc]
      have hq0 := congrArg (fun u : RootTransitionSpace P E => u.2.2) h
      change L z.1 + z.2.1.1 • K z.1 - z.2.1.2 • z.2.2 =
        L w.1 + w.2.1.1 • K w.1 - w.2.1.2 • w.2.2 at hq0
      rw [hp,hd,hc] at hq0
      have hq1 := sub_right_inj.mp hq0
      have hq2 := congrArg (fun v : E => (w.2.1.2)⁻¹ • v) hq1
      simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using hq2
    · exact hs.elim _ _
  exact Prod.ext hp (Prod.ext (Prod.ext hd hc) hq)

end Transition

/-- Recovery from the actual one-child polynomial coefficient operation.
A zero scalar is permitted precisely when the lower numerator space is trivial. -/
theorem pathStepCoefficients_fiber_unique {n : ℕ} (z w : PathPolyData n)
    (hz : z.2.1.2 ≠ 0 ∨ n = 0) (h : pathStepCoefficients z = pathStepCoefficients w) : z = w := by
  have hh := congrArg (parentCoefficientEquiv n) h
  rw [parentCoefficient_step_eq, parentCoefficient_step_eq] at hh
  apply rootTransition_fiber_unique _ _ _ _ z w _ hh
  rcases hz with hz | hn
  · exact Or.inl hz
  · subst n
    right
    refine ⟨fun p q => ?_⟩
    apply (degreeLTEquiv ℝ 0).injective
    funext i
    exact Fin.elim0 i

end HydrologyTree
