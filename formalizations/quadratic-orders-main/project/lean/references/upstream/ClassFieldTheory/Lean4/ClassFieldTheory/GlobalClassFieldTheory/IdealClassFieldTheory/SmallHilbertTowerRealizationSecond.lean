/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealizationNorm

set_option autoImplicit false

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open AlgebraicNumberTheory
open ClassFormation
open CyclicCohomology
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open RamificationTheory
open Reciprocity


attribute [local instance] smallHilbertTowerIdeleClassCommGroup
  smallHilbertTowerNormAmbientAlgebra
  smallHilbertTowerNormAmbientIsGalois

section RationalFixedField

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)


local notation "E" => abstractFixedField ℚ (SeparableClosure ℚ) L.field
local notation "N" => smallHilbertClassFieldNormAmbient E

local notation "E₂" => smallHilbertFiniteGaloisNormNeighborhoodTopField K L

/-- The actual finite Galois norm neighbourhood has abstract norm
subgroup contained in the canonical small-Hilbert subgroup of the
middle fixed field.  This is the source-producing norm-topology input;
no norm-openness premise is assumed. -/
theorem smallHilbertFiniteGaloisNormNeighborhood_normSubgroup_le :
    ∀ a : ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field,
      a ∈ smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup K L →
        a ∈ smallHilbertTowerMiddleNormSubgroup K L := by
  intro a ha
  change
    a ∈ (smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
      rationalIdeleClassRepresentation at ha
  have haMap :
      (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm a ∈
        ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
          rationalIdeleClassRepresentation).map
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              L.field
              (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom :=
    ⟨a, ha, rfl⟩
  have haOrdinary :
      (rationalAbstractFixedFieldIdeleClassEquivFixed L.field
        (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm a ∈
        (_root_.ideleClassNorm E N).range.toAddSubgroup :=
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_mem_ordinaryNormRange
      K L _ haMap
  exact smallHilbertFiniteGaloisNormNeighborhood_ordinaryNorm_le K L haOrdinary

/-- The canonical small-Hilbert subgroup of the actual middle fixed
field is open in the genuine norm topology. -/
theorem smallHilbertNormSubgroupInRationalClassFormation_isNormOpen :
    IsNormOpen rationalIdeleClassRepresentation L.field
      (smallHilbertTowerMiddleNormSubgroup K L :
        Set
          (ambientFixedAddSubgroup
            rationalIdeleClassRepresentation L.field)) := by
  rw [normTopology_addSubgroup_isOpen_iff]
  refine
    ⟨smallHilbertFiniteGaloisNormNeighborhood K L, ?_⟩
  change
    smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup K L ≤
      smallHilbertTowerMiddleNormSubgroup K L
  exact smallHilbertFiniteGaloisNormNeighborhood_normSubgroup_le K L

/-- The second small Hilbert class field as an actual finite abelian
subextension of the literal first-stage field. -/
noncomputable def secondSmallHilbertClassFieldSubextension :
    FiniteAbelianSubextension L.field := by
  let H : FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation L.field :=
    ⟨smallHilbertTowerMiddleNormSubgroup K L,
      smallHilbertNormSubgroupInRationalClassFormation_isNormOpen K L⟩
  exact
    Classical.choose
      (FiniteAbelianSubextension.normSubgroupMap_surjective
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (smallHilbertTowerMiddleFiniteAbstractField K L) H)

/-- The second-stage extension realizes exactly the canonical
small-Hilbert norm subgroup of the actual middle field. -/
@[simp]
theorem secondSmallHilbertClassFieldSubextension_normSubgroup :
    (secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertTowerMiddleNormSubgroup K L := by
  let H : FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation L.field :=
    ⟨smallHilbertTowerMiddleNormSubgroup K L,
      smallHilbertNormSubgroupInRationalClassFormation_isNormOpen K L⟩
  have h :=
    Classical.choose_spec
      (FiniteAbelianSubextension.normSubgroupMap_surjective
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (smallHilbertTowerMiddleFiniteAbstractField K L) H)
  exact congrArg Subtype.val h

private noncomputable abbrev secondSmallHilbertClassFieldTopField : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (secondSmallHilbertClassFieldSubextension K L).below

local notation "T₂" => secondSmallHilbertClassFieldTopField K L

private noncomputable instance
    secondSmallHilbertClassFieldSubextensionQuotientFinite :
    Finite
      (L.field.toSubgroup ⧸
        extensionSubgroup L.field
          (secondSmallHilbertClassFieldSubextension K L).field
          (secondSmallHilbertClassFieldSubextension K L).below) :=
  (secondSmallHilbertClassFieldSubextension K L).finite

private noncomputable instance
    secondSmallHilbertClassFieldTopFiniteDimensional :
    FiniteDimensional E T₂ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field
    (secondSmallHilbertClassFieldSubextension K L).field
    (secondSmallHilbertClassFieldSubextension K L).below
    inferInstance inferInstance

private noncomputable instance
    secondSmallHilbertClassFieldTopScalarTower :
    IsScalarTower ℚ E T₂ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private noncomputable instance
    secondSmallHilbertClassFieldTopAbsoluteFiniteDimensional :
    FiniteDimensional ℚ T₂ :=
  FiniteDimensional.trans ℚ E T₂

private noncomputable instance
    secondSmallHilbertClassFieldTopNumberField :
    NumberField T₂ :=
  NumberField.of_module_finite ℚ T₂

private noncomputable instance
    secondSmallHilbertClassFieldTopIsGalois :
    IsGalois E T₂ :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ) L.field
    (secondSmallHilbertClassFieldSubextension K L).field
    (secondSmallHilbertClassFieldSubextension K L).below
    (secondSmallHilbertClassFieldSubextension K L).normal

private theorem
    secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_actualNormRange :
    ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E T₂).range.toAddSubgroup := by
  change
    (finiteNormSubgroup rationalIdeleClassRepresentation
        L.field
        (secondSmallHilbertClassFieldSubextension K L).field
        (secondSmallHilbertClassFieldSubextension K L).below).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E T₂).range.toAddSubgroup
  exact
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      L.field
      (secondSmallHilbertClassFieldSubextension K L).field
      (secondSmallHilbertClassFieldSubextension K L).below
      (secondSmallHilbertClassFieldSubextension K L).normal

private theorem
    secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_smallHilbertNormSubgroup :
    ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup := by
  let e : Additive (IdeleClassGroup E) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation L.field :=
    rationalAbstractFixedFieldIdeleClassEquivFixed L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)
  let H : AddSubgroup (Additive (IdeleClassGroup E)) :=
    (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup
  let back : AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation L.field) →
      AddSubgroup (Additive (IdeleClassGroup E)) :=
    fun n => n.map e.symm.toAddMonoidHom
  have hNorm :
      back ((secondSmallHilbertClassFieldSubextension K L).normSubgroup
        rationalIdeleClassRepresentation) =
      back (smallHilbertTowerMiddleNormSubgroup K L) :=
    congrArg back (secondSmallHilbertClassFieldSubextension_normSubgroup K L)
  have hCancel : back (smallHilbertTowerMiddleNormSubgroup K L) = H :=
    AddSubgroup.map_comap_eq_self_of_surjective e.symm.surjective H
  exact hNorm.trans hCancel

/-- The actual second small Hilbert class field has exactly the intrinsic
small-Hilbert norm range over the literal middle fixed field. -/
@[simp]
theorem secondSmallHilbertClassFieldSubextension_ideleClassNorm_range :
    (_root_.ideleClassNorm E T₂).range =
      smallHilbertClassFieldNormSubgroup (K := E) := by
  apply Subgroup.toAddSubgroup.injective
  exact
    (secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_actualNormRange
      K L).symm.trans
      (secondSmallHilbertClassFieldSubextension_abstractNormMap_eq_smallHilbertNormSubgroup
        K L)

/-- Compatibility of the typed middle endpoint with the canonical endpoint
used by the conjugation API. -/
theorem smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint :
    smallHilbertTowerMiddleNormSubgroup K L =
      smallHilbertNormSubgroupInRationalClassFormation
        (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field := by
  have hField :
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.field =
        L.field := by
    rfl
  unfold smallHilbertNormSubgroupInRationalClassFormation
  cases hField
  exact smallHilbertTowerMiddleNormSubgroup_eq_map K L


end RationalFixedField
end IdealClassFieldTheory
end GlobalClassFieldTheory
