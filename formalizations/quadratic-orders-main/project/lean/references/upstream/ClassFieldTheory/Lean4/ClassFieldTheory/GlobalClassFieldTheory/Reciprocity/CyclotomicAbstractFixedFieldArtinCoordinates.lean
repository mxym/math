/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinFiniteRestriction


set_option autoImplicit false


open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance]
  cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra
  cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra
  cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal
  abstractFixedFieldCyclotomic_numberField

section FiniteCoordinateHelpers

/-- Opaque three-step equality composition used to keep large dependent
finite-level coordinates out of endpoint proof normalization. -/
private theorem cyclotomicAbstractFixedFieldArtin_eqTransThree
    {α : Type} {a b c d : α}
    (hab : a = b) (hbc : b = c) (hcd : c = d) :
    a = d :=
  hab.trans (hbc.trans hcd)

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractFixedField
    ℚ (SeparableClosure ℚ) H.field

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateRelative
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractRelativeFixedField
    ℚ (SeparableClosure ℚ)
    (rationalCyclotomicFieldInertia_le H.field)

private abbrev cyclotomicAbstractFixedFieldArtinCoordinateLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteLayer H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBase H).algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  LocalClassFieldTheory.abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  NumberField.of_module_finite ℚ
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseSeparableAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (SeparableClosure ℚ) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateRelative H).algebra'

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicCompositum_baseScalarTower H

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateAlgebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ E :=
  E.toIntermediateField.algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateNumberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField E :=
  NumberField.of_module_finite ℚ E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois ℚ E :=
  IsAbelianGalois.of_algHom E.toIntermediateField.val

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateNormal
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Normal ℚ E :=
  E.isGalois.to_normal

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  DivisionRing.toRatAlgebra

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) := by
  let hI := rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_numberField H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerSMul H E

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E

/-- The full abstract Artin symbol whose finite coordinates are compared
below.  Naming this endpoint keeps its relative fixed-field data opaque. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField / ℚ) :=
  abstractFixedFieldCyclotomicRestriction H
    (infiniteGlobalArtinMonoidHom
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)

/-- The rational norm Artin symbol serving as the other full endpoint. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField / ℚ) :=
  rationalCyclotomicZHatGlobalArtin
    (IdeleGroup.norm ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) a)


private noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMapData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    {f : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
        cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
        Gal(E / ℚ) //
      f.comp
          (@globalArtinMonoidHomOfNumberField
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (inferInstance : Field
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
            (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
            (inferInstance : Field
              (abstractFixedFieldCyclotomicFiniteGaloisLayer H E))
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)) =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H))} := by
  have hnat :=
    @globalArtinMonoidHomOfNumberField_norm_restriction
      ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      inferInstance inferInstance
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
  exact
    ⟨(@AlgEquiv.restrictNormalHom
          ℚ inferInstance
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          E inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateNormal E)).comp
        (@AlgEquiv.restrictScalarsHom
          ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance inferInstance inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)),
      hnat⟩

/-- The fixed restriction map from the relative finite layer to one rational
cyclotomic coordinate. -/
private noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMap
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
        cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
      Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).1


private theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    (cyclotomicAbstractFixedFieldArtinCoordinateMap H E).comp
        (globalArtinMonoidHom
          (K := cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (L := abstractFixedFieldCyclotomicFiniteGaloisLayer H E)) =
      (globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).2

/-- Pointwise identification of the named coordinate map with the concrete
two-stage restriction used by the abstract fixed-field comparison. -/
private theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
      cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinCoordinateMap H E σ =
      @IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
        (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
        inferInstance inferInstance inferInstance inferInstance
        (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
        (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateNormal E) σ :=
  rfl

/-- The relative projection, common rational finite value, and rational
infinite projection, with both comparison steps packaged by the generic
provider before this concrete tower becomes opaque. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinCoordinateBridgeData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :=
    @compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateRelative H))
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois H)
      a
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
      E
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality H E)

/-- The abstract endpoint after projection to one finite coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  AlgEquiv.restrictNormalHom E
    (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a)

/-- The relative infinite Artin symbol, restricted to a finite layer and
then mapped to the corresponding rational coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.1

/-- The finite relative Artin symbol mapped to one rational coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinFiniteCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.1

/-- The finite rational Artin coordinate of the idele norm. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.1

/-- Naturality of the finite global Artin map at the concrete cyclotomic
coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateNaturality
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRationalCoordinate H a E := by
  rfl

/-- The rational endpoint after projection to one finite coordinate. -/
private noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.2

/-- The abstract restriction map projected to the concrete finite layer. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := by
  calc
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
        AlgEquiv.restrictNormalHom E
          (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) := rfl
    _ = cyclotomicAbstractFixedFieldArtinCoordinateMap H E
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)) :=
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction
          H E
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)).trans
        (cyclotomicAbstractFixedFieldArtinCoordinateMap_apply H E _).symm
    _ = cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := rfl

/-- Restricting the infinite relative Artin symbol supplies exactly the
finite Artin coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.1

/-- The rational cyclotomic Artin map projected to the same finite
coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E := by
  exact
    (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.2.symm

/-- Equality of the two full endpoints at one opaque finite coordinate. -/
private theorem
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) =
      AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinRationalEndpoint H a) := by
  change
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E
  exact
    cyclotomicAbstractFixedFieldArtin_eqTransThree
      (cyclotomicAbstractFixedFieldArtinCoordinateRestriction H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
        H a E).symm

/-- The finite-coordinate comparison assembled in the rational cyclotomic
inverse limit. -/
theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a =
      cyclotomicAbstractFixedFieldArtinRationalEndpoint H a := by
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  exact
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
      H a Eop.unop

end FiniteCoordinateHelpers


end Reciprocity
end GlobalClassFieldTheory
