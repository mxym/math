/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealApproximation


set_option autoImplicit false


open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- Weak approximation in the precise open local cosets required by the
modulus. -/
theorem exists_principal_quotient_mem_primeTo
    (m : Modulus K) (a : IdeleGroup K) :
    ∃ x : Kˣ,
      a * (IdeleGroup.principalIdele K x)⁻¹ ∈
        idelePrimeToModulusSubgroup m := by
  let U : Set
      ((i : ApproximationPlace m) → approximationCompletion m i) :=
    Set.univ.pi (approximationTarget m a)
  have hUOpen : IsOpen U := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_approximationTarget m a i
  have hUNonempty : U.Nonempty :=
    ⟨approximationTargetPoint m a,
      approximationTargetPoint_mem m a⟩
  obtain ⟨x, hx⟩ :=
    (denseRange_approximationEmbedding m).exists_mem_open
      hUOpen hUNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w₀)
        (m.localInfiniteCongruenceSubgroup w₀) at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_⟩
  constructor
  · apply
      (Modulus.mem_infiniteCongruenceSubgroup_iff_local m
        (a * (IdeleGroup.principalIdele K xu)⁻¹).1).2
    intro w
    have hw :=
      hx (Sum.inr w) (Set.mem_univ (Sum.inr w))
    change
      (x : w.Completion) ∈
        unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w) at hw
    obtain ⟨y, hy, hyx⟩ := hw
    have hprincipal :
        ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w =
          y := by
      apply Units.ext
      calc
        ((ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w :
              w.Completionˣ) : w.Completion) =
            (xu : K) :=
          IdeleGroup.infiniteComponent_principalIdele xu w
        _ = (x : K) := rfl
        _ = (y : w.Completion) := hyx.symm
    change
      ContinuousMulEquiv.piUnits a.1 w *
          (ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w)⁻¹ ∈
        m.localInfiniteCongruenceSubgroup w
    rw [hprincipal]
    exact hy
  · intro v hv
    let vm : ↥m.finitePart.support := ⟨v, hv⟩
    have hvx :=
      hx (Sum.inl vm) (Set.mem_univ (Sum.inl vm))
    change
      FinitePlace.embedding v x ∈
        unitRatioSet (a.2 v)
          (localHigherUnitGroup v (m.finitePart v)) at hvx
    obtain ⟨y, hy, hyx⟩ := hvx
    have hprincipal :
        (IdeleGroup.principalIdele K xu).2 v = y := by
      apply Units.ext
      calc
        (((IdeleGroup.principalIdele K xu).2 v :
            (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            (xu : K) :=
          IdeleGroup.finiteComponent_principalIdele xu v
        _ = (x : K) := rfl
        _ = (y : v.adicCompletion K) := hyx.symm
    change
      a.2 v *
          ((IdeleGroup.principalIdele K xu).2 v)⁻¹ ∈
        localHigherUnitGroup v (m.finitePart v)
    rw [hprincipal]
    exact hy

/-- Approximation identifies the idele group as
`I_K = I_K^(m) Kˣ`. -/
theorem idelePrimeToModulusSubgroup_sup_principalSubgroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  intro a _ha
  obtain ⟨x, hx⟩ :=
    exists_principal_quotient_mem_primeTo m a
  rw [Subgroup.mem_sup]
  refine
    ⟨a * (IdeleGroup.principalIdele K x)⁻¹, hx,
      IdeleGroup.principalIdele K x, ⟨x, rfl⟩, ?_⟩
  group

/-- The natural map from the prime-to-`m` ideles to the full idelic
ray-class quotient. -/
def primeToRayClassProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.mk'
    (m.ideleCongruenceSubgroup ⊔
      IdeleGroup.principalSubgroup K)).comp
    (idelePrimeToModulusSubgroup m).subtype

theorem primeToRayClassProjection_ker (m : Modulus K) :
    (primeToRayClassProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hN :
        (a : IdeleGroup K) ∈
          m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K := by
      rw [← QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_ker.mp ha
    rw [Subgroup.mem_sup] at hN
    obtain ⟨c, hc, p, hp, hcp⟩ := hN
    have hcA :
        c ∈ idelePrimeToModulusSubgroup m :=
      ideleCongruenceSubgroup_le_primeTo m hc
    have hpA :
        p ∈ idelePrimeToModulusSubgroup m := by
      have haA :
          (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        a.property
      have hmul :
          c⁻¹ * (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        (idelePrimeToModulusSubgroup m).mul_mem
          ((idelePrimeToModulusSubgroup m).inv_mem hcA) haA
      rw [← hcp] at hmul
      simpa using hmul
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine
      ⟨⟨c, hcA⟩, ?_, ⟨p, hpA⟩, ?_, ?_⟩
    · exact hc
    · exact hp
    · apply Subtype.ext
      exact hcp
  · intro ha
    apply MonoidHom.mem_ker.mpr
    change
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K) =
        1
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨c, hc, p, hp, rfl⟩ := ha
    apply
      (m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K).mul_mem
    · exact
        (show m.ideleCongruenceSubgroup ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_left) hc
    · exact
      (show IdeleGroup.principalSubgroup K ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_right) hp

theorem primeToRayClassProjection_surjective (m : Modulus K) :
    Function.Surjective (primeToRayClassProjection m) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈ idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K := by
    rw [idelePrimeToModulusSubgroup_sup_principalSubgroup m]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨a, ha, p, hp, hap⟩ := hg
  refine ⟨⟨a, ha⟩, ?_⟩
  change
    QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a =
      QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) g
  rw [← hap, map_mul]
  have hpN :
      p ∈ m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K :=
    (show IdeleGroup.principalSubgroup K ≤
        m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K from le_sup_right) hp
  have hmkp :
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K) p =
        1 := by
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hpN
  rw [hmkp]
  exact
    (mul_one
      (QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a)).symm

/-- Restricting the full idelic ray-class quotient to prime-to-`m`
ideles is an equivalence. -/
def quotientRaySubgroupEquivIdeleRayQuotient
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (primeToRayClassProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (primeToRayClassProjection m)
      (primeToRayClassProjection_surjective m))

/-- The quotient equivalence induced by the idelic ray projection evaluates
on a prime-to-modulus idele class as the original projection. -/
@[simp]
theorem quotientRaySubgroupEquivIdeleRayQuotient_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdeleRayQuotient m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      primeToRayClassProjection m a := by
  rw [quotientRaySubgroupEquivIdeleRayQuotient,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (primeToRayClassProjection m) a

/-- The idelic and ideal-theoretic ray class
groups are canonically multiplicatively equivalent. -/
def rayClassGroupEquivIdealRayClassGroup
    (m : Modulus K) :
    RayClassGroup m ≃* IdealRayClassGroup m :=
  (rayClassGroupEquivIdeleQuotient m).trans
    ((quotientRaySubgroupEquivIdeleRayQuotient m).symm.trans
      (quotientRaySubgroupEquivIdealRayClassGroup m))

end RayClass
