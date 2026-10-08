import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldReciprocity
import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldPrimeSplitting
import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership

/-! A bridge from genuine finite ray class extensions and actual splitting
to actual ray-congruent principal generators. The external class field
dependency is pinned and audited in references/upstream/arithmetic-audit;
this module is compiled in that isolated project, not silently added to
the mathlib-only main project's dependencies. -/

set_option autoImplicit false
open scoped NumberField nonZeroDivisors

namespace Entry002

open ClassFieldTheory NumberField IsDedekindDomain

/-- An actual generator of an integral fractional ideal is integral. -/
theorem arithmeticSupply_integral_principal_generator
    (K : Type) [Field K] [NumberField K] (x : Kˣ) (I : Ideal (𝓞 K))
    (h : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
      (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ a : 𝓞 K, (a : K) = (x : K) ∧ Ideal.span {a} = I := by
  have hx : (x : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← h]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨a, _, ha⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
  refine ⟨a, ha, FractionalIdeal.coeIdeal_injective (K := K) ?_⟩
  change ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [FractionalIdeal.coeIdeal_span_singleton, ha]
  exact h

/-- The generator is a nonzero field element, its ideal is the actual
prime fractional ideal, and its congruence is the actual local higher-unit
and real-positivity condition of the supplied modulus. -/
theorem arithmeticSupply_ray_split_generator_iff
    (K : Type) [Field K] [NumberField K] (m : RayClassModulus K)
    (R : RayClassFieldRealization K m) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    FinitePrimeSplitsCompletely K R.extension v ↔
      ∃ x : Kˣ, IsRayCongruent m x ∧
        toPrincipalIdeal (𝓞 K) K x = finitePrimeFractionalIdeal v := by
  rw [finitePrime_splitsCompletelyInRayClassField_iff K m R v hv,
    ← mem_rayPrincipalIdealSubgroup_iff]
  let I : rayClassPrimeToIdeals m :=
    ⟨finitePrimeFractionalIdeal v, finitePrimeFractionalIdeal_mem_primeTo m v hv⟩
  change (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) I = 1) ↔ _
  exact QuotientGroup.eq_one_iff I

/-- Splitting supplies a ray-congruent generator that belongs to the
actual ring of integers, without assuming integrality as an input. -/
theorem arithmeticSupply_ray_split_integral_generator_iff
    (K : Type) [Field K] [NumberField K] (m : RayClassModulus K)
    (R : RayClassFieldRealization K m) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    FinitePrimeSplitsCompletely K R.extension v ↔
      ∃ (x : Kˣ) (a : 𝓞 K), (a : K) = (x : K) ∧ Ideal.span {a} = v.asIdeal ∧
        IsRayCongruent m x ∧
        toPrincipalIdeal (𝓞 K) K x = finitePrimeFractionalIdeal v := by
  rw [arithmeticSupply_ray_split_generator_iff K m R v hv]
  constructor
  · rintro ⟨x, hx, hI⟩
    have h : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      have hval := congrArg Units.val hI
      simpa [finitePrimeFractionalIdeal] using hval
    obtain ⟨a, ha, hspan⟩ := arithmeticSupply_integral_principal_generator K x v.asIdeal h
    exact ⟨x, a, ha, hspan, hx, hI⟩
  · rintro ⟨x, a, ha, hspan, hx, hI⟩
    exact ⟨x, hx, hI⟩

/-- Every actual modulus has a genuine finite abelian number-field
extension with the splitting/principal-ray-generator criterion. This
neither asserts Chebotarev density nor replaces prime supply by an input. -/
theorem arithmeticSupply_exists_ray_extension_generator_criterion
    (K : Type) [Field K] [NumberField K] (m : RayClassModulus K) :
    ∃ R : RayClassFieldRealization K m,
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ m.finitePart.support),
        FinitePrimeSplitsCompletely K R.extension v ↔
          ∃ (x : Kˣ) (a : 𝓞 K), (a : K) = (x : K) ∧ Ideal.span {a} = v.asIdeal ∧
            IsRayCongruent m x ∧
            toPrincipalIdeal (𝓞 K) K x = finitePrimeFractionalIdeal v := by
  obtain ⟨R⟩ := rayClassField_reciprocity K m
  exact ⟨R, fun v hv => arithmeticSupply_ray_split_integral_generator_iff K m R v hv⟩

end Entry002
