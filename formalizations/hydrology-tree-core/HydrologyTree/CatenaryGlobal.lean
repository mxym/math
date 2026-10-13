import HydrologyTree.CatenaryOrientation
import HydrologyTree.RootRecovery

/-! Global uniqueness of the entire real coefficient fiber at every nonsingular
endpoint-path model. The second model is arbitrary, not assumed regular or positive.
This is stronger than a local inverse-function conclusion, but does not assert
existence of a realization for an arbitrary prescribed response. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

def PathRegularRates (n : ℕ) (x : TreeRates n) : Prop :=
  (∀ i : Fin n, x.1 i.succ ≠ 0) ∧
  (∀ i : Fin n, i.val+1 < n → x.2 i ≠ 0)

/-- The exact algebraic regularity conditions imply uniqueness of the entire
real fiber of the original unreduced physical coefficient map. -/
theorem catenary_coefficient_fiber_unique (n : ℕ) (x y : TreeRates n)
    (hx : PathRegularRates n x) (hxy : pathCoefficientMap n x = pathCoefficientMap n y) : x = y := by
  induction n with
  | zero =>
    have hleak := physical_root_leak_identified (pathTree 0) x y hx.1 hxy
    apply Prod.ext
    · funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      exact hleak
    · funext i
      exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨⟨u,ell,f⟩,rfl⟩ := (prependRateEquiv n).surjective x
    obtain ⟨⟨v,ell',g⟩,rfl⟩ := (prependRateEquiv n).surjective y
    have hell : ell = ell' := physical_root_leak_identified (pathTree (n+1))
      (prependRateEquiv n (u,(ell,f))) (prependRateEquiv n (v,(ell',g))) hx.1 hxy
    have hs : u.1 0 * f ≠ 0 ∨ n = 0 := by
      by_cases hn : n = 0
      · exact Or.inr hn
      · left
        apply mul_ne_zero
        · exact hx.1 0
        · exact hx.2 0 (by simp only [Fin.val_zero]; omega)
    have hstep := hxy
    rw [pathCoefficientMap_recursion, pathCoefficientMap_recursion] at hstep
    have hdata := pathStepCoefficients_fiber_unique
      ((pathCoefficientMap n u).1,((ell+f,u.1 0*f),(pathCoefficientMap n u).2))
      ((pathCoefficientMap n v).1,((ell'+g,v.1 0*g),(pathCoefficientMap n v).2)) hs hstep
    have hchild : pathCoefficientMap n u = pathCoefficientMap n v := by
      apply Prod.ext
      · exact congrArg (fun z : PathPolyData n => z.1) hdata
      · exact congrArg (fun z : PathPolyData n => z.2.2) hdata
    have hu : PathRegularRates n u := by
      constructor
      · intro i
        exact hx.1 i.succ
      · intro i hi
        exact hx.2 i.succ (by simp only [Fin.val_succ]; omega)
    have huv : u = v := ih u v hu hchild
    have hd : ell+f = ell'+g := congrArg (fun z : PathPolyData n => z.2.1.1) hdata
    have hfg : f = g := by linarith
    rw [huv,hell,hfg]

/-- No regularity assumption is placed on the alternative real model. -/
theorem catenary_global_fiber_at_regular_point (n : ℕ) (x : TreeRates n)
    (hx : catenaryCanonicalJacobian n x ≠ 0) :
    ∀ y : TreeRates n, pathCoefficientMap n y = pathCoefficientMap n x → y = x := by
  have hr : PathRegularRates n x := by
    constructor
    · intro i hi
      exact hx ((catenary_standard_singular_locus n x).mpr (Or.inl ⟨i,hi⟩))
    · intro i hi h0
      exact hx ((catenary_standard_singular_locus n x).mpr (Or.inr ⟨i,hi,h0⟩))
  intro y hy
  exact (catenary_coefficient_fiber_unique n x y hr hy.symm).symm

/-- Every strictly positive internal-rate endpoint path has a singleton real
coefficient fiber, not only a singleton fiber among positive competitors. -/
theorem catenary_positive_global_identification (n : ℕ) (x : TreeRates n)
    (ha : ∀ i : Fin n, 0 < x.1 i.succ) (hf : ∀ i : Fin n, 0 < x.2 i) :
    ∀ y : TreeRates n, pathCoefficientMap n y = pathCoefficientMap n x → y = x := by
  have hr : PathRegularRates n x := ⟨fun i => ne_of_gt (ha i),fun i _ => ne_of_gt (hf i)⟩
  intro y hy
  exact (catenary_coefficient_fiber_unique n x y hr hy.symm).symm

end HydrologyTree
