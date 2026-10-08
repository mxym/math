/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidueEmbeddedReciprocity


set_option autoImplicit false


open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory


variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)

local instance abstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance abstractFixedFieldRelativeQuotientFinite :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K.field L.field L.below) :=
  L.finite

local instance abstractFixedFieldRelativeQuotientIsMulCommutative :
    IsMulCommutative L.extensionQuotient :=
  L.commutative

noncomputable local instance abstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance abstractRelativeFixedFieldFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

local instance abstractFixedFieldRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance abstractRelativeFixedFieldAbsoluteFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance abstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

/-- The lower fixed idèle-class group is commutative.  Naming the mixin
before the public quotient declarations avoids delayed normality synthesis
inside their definition bodies. -/
local instance
    abstractFixedFieldIdeleClassGroupIsMulCommutative :
    IsMulCommutative
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

noncomputable local instance abstractRelativeFixedFieldNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

/-- Use the same explicit Galois witness as the fixed-field quotient
comparison.  Deriving it through `IsAbelianGalois` produces an equivalent
but much larger dependent instance path. -/
noncomputable local instance
    abstractRelativeFixedFieldIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

noncomputable local instance abstractRelativeFixedFieldIsAbelianGalois :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

/-- Use one opaque normality witness for the actual fixed-field norm range.
This keeps every occurrence of its quotient group on the same instance path. -/
local instance
    abstractFixedFieldIdeleClassNormRangeNormal :
    ((_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below)).range).Normal := by
  infer_instance

/-- The abelianized abstract extension quotient is the actual Galois
group of the corresponding pair of fixed fields. -/
noncomputable def
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    Additive
        (Abelianization
          (FiniteGaloisSubextension.extensionQuotient
            L.toFiniteGaloisExtension)) ≃+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let e :
      L.extensionQuotient ≃*
        Gal(E / F) :=
    L.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below L.normal)
  exact
    MulEquiv.toAdditive
      ((Abelianization.equivOfComm :
          L.extensionQuotient ≃*
            Abelianization L.extensionQuotient).symm.trans e)

/-- The actual fixed-field global norm-residue equivalence

`C_F / N_{E/F} C_E ≃ Gal(E/F)`

attached to an abstract finite abelian subextension in the rational
absolute class formation. -/
noncomputable def abstractFixedFieldGlobalNormResidueEquiv :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range) ≃+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let eNorm :
      FiniteNormQuotient rationalIdeleClassRepresentation
          K.field L.field L.below ≃+
        Additive
          (Abelianization L.toFiniteGaloisExtension.extensionQuotient) :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K L.toFiniteGaloisExtension
  exact
    (rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K.field L.field L.below L.normal).symm.trans
      (eNorm.trans
        (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
          K L))

/-- The abstract finite norm-residue equivalence with its dependent source
instance fixed to the public finite norm quotient. -/
noncomputable def abstractFixedFieldFiniteNormResidueGaloisEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) := by
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      K.field L.field L.below
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below)
      (Additive
        (Abelianization
          L.toFiniteGaloisExtension.extensionQuotient))
      (Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L.toFiniteGaloisExtension)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
        K L)

/-- The abstract norm-residue symbol on the fixed part of the rational
absolute idele-class representation, with its value transported to the
actual Galois group of the two fixed fields.  This is the form consumed
directly by the abstract norm--restriction naturality theorem. -/
noncomputable def ambientFixedGlobalNormResidueAddMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field →+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  exact
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).toAddMonoidHom.comp
      (finiteNormClassHom rationalIdeleClassRepresentation
        K.field L.field L.below)

/-- The ordinary idele class group of the lower fixed field, transported
to the fixed part of the rational absolute idele-class representation. -/
private noncomputable def abstractFixedFieldIdeleClassToAmbientFixedMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    IdeleClassGroup F →*
      Multiplicative
        (ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field) :=
  (rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).toAddMonoidHom.toMultiplicativeRight

/-- The actual norm-residue homomorphism on the ordinary idele class
group of the lower fixed field, constructed without choosing a second
field embedding. -/
noncomputable def abstractFixedFieldGlobalNormResidueMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    IdeleClassGroup F →* Gal(E / F) :=
  (ambientFixedGlobalNormResidueAddMonoidHom K L).toMultiplicative.comp
    (abstractFixedFieldIdeleClassToAmbientFixedMonoidHom K)

/-- Pointwise form of the ambient fixed-part norm-residue homomorphism. -/
theorem ambientFixedGlobalNormResidueAddMonoidHom_apply
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    ambientFixedGlobalNormResidueAddMonoidHom K L a =
      abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L.toFiniteGaloisExtension
          (finiteNormClass rationalIdeleClassRepresentation
            K.field L.field L.below a)) := by
  change
    abstractFixedFieldFiniteNormResidueGaloisEquiv K L
        (finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below a) = _
  rfl

/-- Pointwise form of the transported fixed-field norm-residue homomorphism. -/
private theorem abstractFixedFieldGlobalNormResidueMonoidHom_apply :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    ∀ c : IdeleClassGroup F,
      abstractFixedFieldGlobalNormResidueMonoidHom K L c =
        Additive.toMul
          (ambientFixedGlobalNormResidueAddMonoidHom K L
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
              (Additive.ofMul c))) := by
  dsimp only
  intro c
  rfl

/-- Transporting an ordinary fixed-field idele class to the ambient
fixed part and applying the abstract norm-residue map gives exactly the
actual fixed-field norm-residue value. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    abstractFixedFieldGlobalNormResidueMonoidHom K L
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm a)) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a) := by
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_apply]
  change
    Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            ((rationalAbstractFixedFieldIdeleClassEquivFixed
              K.field).symm a))) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a)
  rw [(rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).apply_symm_apply]


end Reciprocity
end GlobalClassFieldTheory
