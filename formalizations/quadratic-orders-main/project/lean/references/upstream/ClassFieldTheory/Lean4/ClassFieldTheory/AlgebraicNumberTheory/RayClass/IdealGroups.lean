/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Ring.Compact


set_option autoImplicit false


open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- Fractional ideals having valuation zero at every finite prime in the
support of the modulus. -/
def primeToModulusIdeals (m : Modulus K) :
    Subgroup (FractionalIdealGroup K) where
  carrier := {I | ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0}
  one_mem' v _ := FractionalIdeal.count_one K v
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul,
      FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J),
      hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K v,
      hI v hv, neg_zero]

@[simp]
theorem mem_primeToModulusIdeals_iff
    (m : Modulus K) (I : FractionalIdealGroup K) :
    I ∈ primeToModulusIdeals m ↔
      ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count K v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
  Iff.rfl

/-- A finite prime outside the support of `m`, regarded as an element of
the group of fractional ideals prime to `m`. -/
def primeToModulusIdeal
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    primeToModulusIdeals m :=
  ⟨FractionalIdealGroup.prime v, by
    intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      FractionalIdeal.count K w
          (v.asIdeal :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        0
    exact
      FractionalIdeal.count_maximal_coprime
        K w hwv.symm⟩

/-- Coercing a prime outside the modulus support recovers its prime
fractional ideal. -/
@[simp]
theorem primeToModulusIdeal_coe
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    (primeToModulusIdeal m v hv :
        FractionalIdealGroup K) =
      FractionalIdealGroup.prime v :=
  rfl

/-- Finite ideles satisfying the higher-unit condition at every prime in
the support of the modulus. -/
def finitePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∈ m.finitePart.support →
    a v ∈ localHigherUnitGroup v (m.finitePart v)}
  one_mem' v _ := (localHigherUnitGroup v (m.finitePart v)).one_mem
  mul_mem' ha hb v hv :=
    (localHigherUnitGroup v (m.finitePart v)).mul_mem (ha v hv) (hb v hv)
  inv_mem' ha v hv :=
    (localHigherUnitGroup v (m.finitePart v)).inv_mem (ha v hv)

/-- Ideles satisfying the infinite positivity and finite higher-unit
conditions of a modulus. -/
def idelePrimeToModulusSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup K) :=
  m.infiniteCongruenceSubgroup.prod
    (finitePrimeToModulusSubgroup m)

theorem localHigherUnitGroup_le_integralUnits
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

theorem fractionalIdeal_mem_primeToModulusIdeals
    (m : Modulus K) (a : IdeleGroup K)
    (ha : a ∈ idelePrimeToModulusSubgroup m) :
    IdeleGroup.fractionalIdeal a ∈ primeToModulusIdeals m := by
  intro v hv
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector a.2) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v (a.2 v)).2
  exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v hv)

/-- The fractional-ideal map restricted to ideles prime to a modulus. -/
def primeToIdealMap (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      primeToModulusIdeals m where
  toFun a :=
    ⟨IdeleGroup.fractionalIdeal a,
      fractionalIdeal_mem_primeToModulusIdeals m a a.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

/-- A finite idele with a prescribed valuation vector away from the
support of a modulus and value one on its support. -/
def valuationVectorSectionPrimeTo
    (m : Modulus K)
  (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  ⟨fun v =>
      if v ∈ m.finitePart.support then 1
      else FiniteIdeleGroup.chosenLocalOrderSection v (e v), by
    filter_upwards
      [m.finitePart.support.eventually_cofinite_notMem,
        e.support.eventually_cofinite_notMem] with v hvm he
    simp only [hvm, ↓reduceIte]
    apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).1
    rw [FiniteIdeleGroup.localOrder_chosenLocalOrderSection,
      Finsupp.notMem_support_iff.mp he]⟩

theorem valuationVector_valuationVectorSectionPrimeTo
    (m : Modulus K)
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, v ∈ m.finitePart.support → e v = 0) :
    FiniteIdeleGroup.valuationVector
        (valuationVectorSectionPrimeTo m e) =
      Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  ext v
  rw [FiniteIdeleGroup.valuationVector_apply]
  by_cases hv : v ∈ m.finitePart.support
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_left hv, map_one]
    exact (he v hv).symm
  · change
      (FiniteIdeleGroup.localOrder v
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v))).toAdd =
        e v
    rw [ite_eq_right hv,
      FiniteIdeleGroup.localOrder_chosenLocalOrderSection]

theorem primeToIdealMap_surjective (m : Modulus K) :
    Function.Surjective (primeToIdealMap m) := by
  intro I
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    FractionalIdealGroup.countVector (I : FractionalIdealGroup K)
  have he : ∀ v, v ∈ m.finitePart.support → e v = 0 := by
    intro v hv
    exact I.property v hv
  let a : IdeleGroup K :=
    (1, valuationVectorSectionPrimeTo m e)
  have ha : a ∈ idelePrimeToModulusSubgroup m := by
    constructor
    · exact m.infiniteCongruenceSubgroup.one_mem
    · intro v hv
      change
        (if v ∈ m.finitePart.support then 1
          else FiniteIdeleGroup.chosenLocalOrderSection v (e v)) ∈
            localHigherUnitGroup v (m.finitePart v)
      rw [ite_eq_left hv]
      exact (localHigherUnitGroup v (m.finitePart v)).one_mem
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  apply FractionalIdealGroup.ext_count
  intro v
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (valuationVectorSectionPrimeTo m e)) :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        ((I : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [valuationVector_valuationVectorSectionPrimeTo m e he,
    FractionalIdealGroup.count_factorization]
  exact FractionalIdealGroup.countVector_apply I v

theorem ideleCongruenceSubgroup_le_primeTo
    (m : Modulus K) :
    m.ideleCongruenceSubgroup ≤
      idelePrimeToModulusSubgroup m := by
  intro a ha
  exact ⟨ha.1, fun v _ => ha.2 v⟩

/-- The congruence subgroup, viewed inside the subgroup of ideles prime
to the modulus. -/
def congruenceSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  m.ideleCongruenceSubgroup.subgroupOf
    (idelePrimeToModulusSubgroup m)

theorem primeToIdealMap_ker (m : Modulus K) :
    (primeToIdealMap m).ker =
      congruenceSubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hintegral :
        (a : IdeleGroup K) ∈
          IdeleGroup.integralAtFinitePlaces (K := K) := by
      rw [← IdeleGroup.fractionalIdeal_ker,
        MonoidHom.mem_ker]
      exact congrArg Subtype.val
        (MonoidHom.mem_ker.mp ha)
    constructor
    · exact a.property.1
    · intro v
      by_cases hv : v ∈ m.finitePart.support
      · exact a.property.2 v hv
      · rw [Finsupp.notMem_support_iff.mp hv,
          localHigherUnitGroup_zero]
        exact hintegral v
  · intro ha
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal (a : IdeleGroup K) = 1
    rw [← MonoidHom.mem_ker,
      IdeleGroup.fractionalIdeal_ker]
    intro v
    exact localHigherUnitGroup_le_integralUnits v (m.finitePart v) (ha.2 v)

/-- The quotient of ideles prime to a modulus by the congruence subgroup,
identified with fractional ideals prime to the modulus. -/
def quotientCongruenceEquivPrimeToIdeals (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        congruenceSubgroupInPrimeTo m ≃*
      primeToModulusIdeals m := by
  rw [← primeToIdealMap_ker m]
  exact QuotientGroup.quotientKerEquivOfSurjective
    (primeToIdealMap m) (primeToIdealMap_surjective m)

/-- Principal ideles satisfying the modulus conditions, considered inside
`I_K^(m)`. -/
def principalSubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  Subgroup.comap (idelePrimeToModulusSubgroup m).subtype
    (IdeleGroup.principalSubgroup K)

/-- Principal ideals generated by a totally positive element congruent to
one modulo the finite modulus. -/
def principalRayIdealSubgroup (m : Modulus K) :
    Subgroup (primeToModulusIdeals m) :=
  Subgroup.map (primeToIdealMap m)
    (principalSubgroupInPrimeTo m)

theorem mem_principalRayIdealSubgroup_iff
    (m : Modulus K) (I : primeToModulusIdeals m) :
    I ∈ principalRayIdealSubgroup m ↔
      ∃ x : Kˣ,
        ∃ _hx : IdeleGroup.principalIdele K x ∈
          idelePrimeToModulusSubgroup m,
        toPrincipalIdeal (𝓞 K) K x =
          (I : FractionalIdealGroup K) := by
  constructor
  · rintro ⟨a, ha, hmap⟩
    obtain ⟨x, hx⟩ := ha
    refine ⟨x, ?_, ?_⟩
    · rw [hx]
      exact a.property
    · have hval := congrArg Subtype.val hmap
      change IdeleGroup.fractionalIdeal (a : IdeleGroup K) =
        (I : FractionalIdealGroup K) at hval
      rw [← IdeleGroup.fractionalIdeal_principalIdele]
      exact (congrArg (IdeleGroup.fractionalIdeal (K := K)) hx).trans hval
  · rintro ⟨x, hx, hideal⟩
    let a : idelePrimeToModulusSubgroup m :=
      ⟨IdeleGroup.principalIdele K x, hx⟩
    have ha : a ∈ principalSubgroupInPrimeTo m := by
      change IdeleGroup.principalIdele K x ∈
        IdeleGroup.principalSubgroup K
      exact ⟨x, rfl⟩
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    change IdeleGroup.fractionalIdeal
        (IdeleGroup.principalIdele K x) =
      (I : FractionalIdealGroup K)
    rw [IdeleGroup.fractionalIdeal_principalIdele, hideal]

/-- The ideal-theoretic ray class group `J_K^m / P_K^m`. -/
abbrev IdealRayClassGroup (m : Modulus K) :=
  primeToModulusIdeals m ⧸ principalRayIdealSubgroup m

/-- The canonical projection from ideles prime to the modulus to the
ideal-theoretic ray class group. -/
def idealRayProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdealRayClassGroup m :=
  (QuotientGroup.mk' (principalRayIdealSubgroup m)).comp
    (primeToIdealMap m)

/-- The subgroup generated by congruence ideles and principal ideles
inside the ideles prime to a modulus. -/
def raySubgroupInPrimeTo (m : Modulus K) :
    Subgroup (idelePrimeToModulusSubgroup m) :=
  congruenceSubgroupInPrimeTo m ⊔
    principalSubgroupInPrimeTo m

theorem idealRayProjection_surjective (m : Modulus K) :
    Function.Surjective (idealRayProjection m) := by
  intro c
  obtain ⟨I, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (principalRayIdealSubgroup m) c
  obtain ⟨a, rfl⟩ := primeToIdealMap_surjective m I
  exact ⟨a, rfl⟩

theorem idealRayProjection_ker (m : Modulus K) :
    (idealRayProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m a) = 1 at ha
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    let n : idelePrimeToModulusSubgroup m := a * p⁻¹
    have hn : n ∈ congruenceSubgroupInPrimeTo m := by
      rw [← primeToIdealMap_ker m, MonoidHom.mem_ker]
      change primeToIdealMap m (a * p⁻¹) = 1
      rw [map_mul, map_inv, hpa]
      simp
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine ⟨n, hn, p, hp, ?_⟩
    dsimp [n]
    group
  · intro ha
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨n, hn, p, hp, rfl⟩ := ha
    change QuotientGroup.mk'
        (principalRayIdealSubgroup m)
        (primeToIdealMap m (n * p)) = 1
    rw [map_mul]
    have hn' : primeToIdealMap m n = 1 :=
      MonoidHom.mem_ker.mp
        ((primeToIdealMap_ker m).symm ▸ hn)
    rw [hn', one_mul]
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨p, hp, rfl⟩

/-- The quotient of ideles prime to the modulus by the full ray subgroup,
identified with the ideal-theoretic ray class group. -/
def quotientRaySubgroupEquivIdealRayClassGroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdealRayClassGroup m :=
  (QuotientGroup.quotientMulEquivOfEq
      (idealRayProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (idealRayProjection m)
      (idealRayProjection_surjective m))

/-- The quotient equivalence induced by the ideal-ray projection evaluates on
the class of a prime-to-modulus idele as the original projection. -/
@[simp]
theorem quotientRaySubgroupEquivIdealRayClassGroup_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdealRayClassGroup m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      idealRayProjection m a := by
  rw [quotientRaySubgroupEquivIdealRayClassGroup,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (idealRayProjection m) a


end RayClass
