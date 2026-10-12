/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryFieldNormRestriction
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedLocalGlobalCompatibility
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm


set_option autoImplicit false


open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]


local instance splitFactPrimeFixedFields (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra
  finitePadicAuxiliaryExtensionNormal
  finitePadicAuxiliaryExtensionQuotientFinite
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

/-- Generation of the actual finite Galois group transports back
through the compatible finite quotient coordinate. -/
theorem
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (σ : Gal(L / K))
    (hτσ :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ)
    (hσ : Subgroup.closure ({σ} : Set (Gal(L / K))) = ⊤) :
    Subgroup.closure
        ({numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ} :
          Set
            ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
              extensionSubgroup
                (numberFieldTowerBaseSubgroup K L)
                (numberFieldTowerTopSubgroup L)
                (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
      ⊤ := by
  let e :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  let q :
      (numberFieldTowerFiniteGaloisSubextension
        K L).extensionQuotient :=
    numberFieldTowerFiniteQuotientCoordinate
      (K := K) (L := L) τ
  have hq : e.toMonoidHom q = σ := by
    exact hτσ
  change
    Subgroup.closure
        ({q} :
          Set
            (numberFieldTowerFiniteGaloisSubextension
              K L).extensionQuotient) =
      ⊤
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [MonoidHom.map_closure, Set.image_singleton,
    hq, hσ,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- If the finite quotient coordinate of a lift generates the whole
finite Galois quotient, then its cyclic preimage together with the
top-field subgroup generates the whole embedded absolute Galois
group. -/
theorem
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ⊔
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) =
      ⊤ := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let finiteProjection :
      P.toSubgroup →*
        Q :=
    (MonoidHom.fst Q
      (Multiplicative ℤ_[p.1])).comp
        P.toSubgroup.subtype
  have hprojection :
      Γ.toSubgroup.map finiteProjection = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    apply (Subgroup.closure_le _).2
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    refine
      ⟨γ,
        (ClassFormation.padicCyclicClosureGenerator γ).2,
        ?_⟩
    rfl
  have hquotientSurjective :
      ∀ q : Q,
        ∃ u : H.toSubgroup,
          u ∈
              (numberFieldTowerFinitePadicCyclicPreimage
                (K := K) (L := L) p τ).toSubgroup ∧
            numberFieldTowerFiniteQuotientCoordinate
                (K := K) (L := L) u =
              q := by
    intro q
    have hq :
        q ∈ Γ.toSubgroup.map finiteProjection := by
      rw [hprojection]
      trivial
    obtain ⟨z, hzΓ, hzq⟩ := hq
    obtain ⟨u, hu⟩ :=
      numberFieldTowerFinitePadicRangeRestriction_surjective
        (K := K) (L := L) p z
    refine ⟨u, ?_, ?_⟩
    · change rangeRestriction u ∈ Γ.toSubgroup
      rw [hu]
      exact hzΓ
    · calc
        numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) u =
            finiteProjection (rangeRestriction u) := rfl
        _ = finiteProjection z := congrArg finiteProjection hu
        _ = q := hzq
  apply top_unique
  intro h _
  obtain ⟨u, huU, huq⟩ :=
    hquotientSurjective
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) h)
  let k : H.toSubgroup :=
    h * u⁻¹
  have hkN : k ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) k).mp
    change
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) (h * u⁻¹) =
        1
    rw [map_mul, map_inv, huq, mul_inv_cancel]
  have hkSup :
      k ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_right :
      N ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) hkN
  have huSup :
      u ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_left :
      (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) huU
  have hku :
      k * u = h := by
    simp only [k, inv_mul_cancel_right]
  rw [← hku]
  exact
    ((numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ).toSubgroup ⊔ N).mul_mem
      hkSup huSup

/-- Ambient form of the generation statement: the auxiliary cyclic
fixed subgroup together with the subgroup fixing `L` generates the
subgroup fixing `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ⊔
        (numberFieldTowerTopSubgroup L).toSubgroup =
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup
      H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  have hrelative :
      U.toSubgroup ⊔ N = ⊤ :=
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
      (K := K) (L := L) p τ hgenerate
  have hNmap :
      N.map H.toSubgroup.subtype =
        T.toSubgroup := by
    exact
      Subgroup.map_subgroupOf_eq_of_le
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  change
    U.toSubgroup.map H.toSubgroup.subtype ⊔
        T.toSubgroup =
      H.toSubgroup
  rw [← hNmap, ← Subgroup.map_sup,
    hrelative, ← MonoidHom.range_eq_map,
    H.toSubgroup.range_subtype]

/-- The concrete auxiliary fixed field is linearly disjoint from `L`
over the compatible embedded copy of `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedField_inf_topField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let H :=
    numberFieldTowerBaseSubgroup K L
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L),
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldTowerBaseField K L)]
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        IntermediateField.fixedField T.toSubgroup =
      IntermediateField.fixedField H.toSubgroup
  rw [
    ← IntermediateField.fixedField_sup_eq_inf,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
      (K := K) (L := L) p τ hgenerate]

/-- If the finite quotient coordinate is `p`-primary, adjoining the
actual rational `p`-primary cyclotomic field to the auxiliary fixed
field contains the compatible copy of `L`.

This is the field-theoretic conclusion of the simultaneous
finite/cyclotomic lift: the intersection of the two fixing subgroups
already fixes `L`, hence their fixed-field compositum contains `L`. -/
theorem
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    numberFieldInRationalSeparableClosure L ≤
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊔
        rationalCyclotomicPadicField p := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  let C : @IntermediateField ℚ (SeparableClosure ℚ) _ _
      rationalSeparableClosureAlgebra :=
    rationalCyclotomicPadicField p
  have hfixing :
      (F ⊔ C).fixingSubgroup ≤
        T.toSubgroup := by
    change
      (IntermediateField.fixedField S.toSubgroup ⊔ C).fixingSubgroup ≤
        T.toSubgroup
    rw [
      IntermediateField.fixingSubgroup_sup,
      InfiniteGalois.fixingSubgroup_fixedField S]
    intro σ hσ
    apply
      numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
        (K := K) (L := L) p τ n hn hdegree hprimary
    refine ⟨hσ.1, ?_⟩
    let : Algebra ℚ rationalCyclotomicZHatField :=
      rationalCyclotomicZHatField.algebra'
    let : @Normal ℚ rationalCyclotomicZHatField _ _
        rationalCyclotomicZHatField.algebra' :=
      rationalCyclotomicZHatField_normal
    let E :=
      rationalCyclotomicPadicFieldWithinZHat p
    change
      rationalCyclotomicPadicCoordinate p
          (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) =
        1
    have hr :
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ ∈
          E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have hfix :
          σ x.1 = x.1 :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IntermediateField.lift E) σ).1 hσ.2 x.1
            ((IntermediateField.mem_lift x).2 hx)
      exact
        (AlgEquiv.restrictNormal_commutes
          σ rationalCyclotomicZHatField x).trans hfix
    rw [rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup]
      at hr
    exact hr
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L)]
  change
    IntermediateField.fixedField T.toSubgroup ≤
      F ⊔ C
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (F ⊔ C)]
  exact
    IntermediateField.fixedField_le hfixing

end Reciprocity
end GlobalClassFieldTheory
