/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealizationEmbedding

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

private noncomputable def rebaseFiniteGaloisSubextension
    {G : Type} [Group G] [TopologicalSpace G]
    {B B' : ClosedSubgroup G} (h : B = B')
    (P : FiniteGaloisSubextension B) :
    FiniteGaloisSubextension B' :=
  h ▸ P

@[simp]
private theorem rebaseFiniteGaloisSubextension_field
    {G : Type} [Group G] [TopologicalSpace G]
    {B B' : ClosedSubgroup G} (h : B = B')
    (P : FiniteGaloisSubextension B) :
    (rebaseFiniteGaloisSubextension h P).field = P.field := by
  cases h
  rfl

private theorem
    rebaseRationalFiniteGaloisSubextension_fixedField_eq
    {B B' : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (h : B = B') (P : FiniteGaloisSubextension B) :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rebaseFiniteGaloisSubextension h P).below).restrictScalars ℚ =
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          P.below).restrictScalars ℚ := by
  cases h
  rfl

/-- An actual finite Galois norm neighbourhood over the literal
first-stage subgroup.  It is produced by the finite-index Kummer
construction and the controlled embedding above. -/
noncomputable def smallHilbertFiniteGaloisNormNeighborhood :
    FiniteGaloisSubextension L.field :=
  rebaseFiniteGaloisSubextension
    (smallHilbertNormNeighborhoodEmbeddedBase_eq K L)
    (smallHilbertFiniteGaloisNormNeighborhoodRaw K L)


/-- The norm subgroup of the small Hilbert norm-neighborhood extension
in the ambient fixed idele-class representation. -/
noncomputable def smallHilbertFiniteGaloisNormNeighborhoodNormSubgroup :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field) :=
  (smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
    rationalIdeleClassRepresentation

/-- The relative fixed field realizing the top field of the small
Hilbert norm-neighborhood extension. -/
noncomputable abbrev
    smallHilbertFiniteGaloisNormNeighborhoodTopField : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (smallHilbertFiniteGaloisNormNeighborhood K L).below

local notation "E₂" =>
  smallHilbertFiniteGaloisNormNeighborhoodTopField K L

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodQuotientFinite :
    Finite
      (L.field.toSubgroup ⧸
        extensionSubgroup L.field
          (smallHilbertFiniteGaloisNormNeighborhood K L).field
          (smallHilbertFiniteGaloisNormNeighborhood K L).below) :=
  (smallHilbertFiniteGaloisNormNeighborhood K L).finite

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodFiniteDimensional :
    FiniteDimensional E E₂ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field
    (smallHilbertFiniteGaloisNormNeighborhood K L).field
    (smallHilbertFiniteGaloisNormNeighborhood K L).below
    inferInstance inferInstance

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodScalarTower :
    IsScalarTower ℚ E E₂ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodAbsoluteFiniteDimensional :
    FiniteDimensional ℚ E₂ :=
  FiniteDimensional.trans ℚ E E₂

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodNumberField :
    NumberField E₂ :=
  NumberField.of_module_finite ℚ E₂

private noncomputable instance
    smallHilbertFiniteGaloisNormNeighborhoodIsGalois :
    IsGalois E E₂ :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ) L.field
    (smallHilbertFiniteGaloisNormNeighborhood K L).field
    (smallHilbertFiniteGaloisNormNeighborhood K L).below
    (smallHilbertFiniteGaloisNormNeighborhood K L).normal

private theorem
    smallHilbertFiniteGaloisNormNeighborhood_fixedField_eq_range :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ =
        AlgHom.fieldRange
          (smallHilbertNormNeighborhoodEmbedding K L) := by
  rw [show
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ =
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (smallHilbertFiniteGaloisNormNeighborhoodRaw K L).below).restrictScalars ℚ
    from
      rebaseRationalFiniteGaloisSubextension_fixedField_eq
        (smallHilbertNormNeighborhoodEmbeddedBase_eq K L)
        (smallHilbertFiniteGaloisNormNeighborhoodRaw K L)]
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange
        (smallHilbertNormNeighborhoodEmbedding K L))

private noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv :
    N ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (smallHilbertFiniteGaloisNormNeighborhood K L).below).restrictScalars ℚ :=
  (smallHilbertNormNeighborhoodEmbedding K L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (smallHilbertFiniteGaloisNormNeighborhood_fixedField_eq_range
        K L).symm)

@[simp]
private theorem
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv_algebraMap
    (x : E) :
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv K L
        (algebraMap E N x) =
      algebraMap E
        E₂ x := by
  apply Subtype.ext
  change
    smallHilbertNormNeighborhoodEmbedding K L
        (algebraMap E N x) =
      (x : SeparableClosure ℚ)
  exact smallHilbertNormNeighborhoodEmbedding_algebraMap K L x

private noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodRelativeTopEquiv :
    N ≃ₐ[E] E₂ := {
  smallHilbertFiniteGaloisNormNeighborhoodTopEquiv K L with
  commutes' := fun x =>
    smallHilbertFiniteGaloisNormNeighborhoodTopEquiv_algebraMap
      K L x }

theorem
    smallHilbertFiniteGaloisNormNeighborhood_ordinaryNorm_le :
    (_root_.ideleClassNorm E N).range ≤
      smallHilbertClassFieldNormSubgroup (K := E) := by
  simpa only [smallHilbertClassFieldNormAmbient] using
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (K := E) (smallHilbertClassFieldNormSubgroup (K := E))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := E)))

private theorem
    smallHilbertFiniteGaloisNormNeighborhood_ordinaryNormRange_eq :
    (_root_.ideleClassNorm E N).range =
      (_root_.ideleClassNorm E E₂).range := by
  simpa only [ordinaryIdeleClassNorm_range_eq_relative] using
    (ideleClassNorm_range_algEquiv
      (K := E)
      (smallHilbertFiniteGaloisNormNeighborhoodRelativeTopEquiv
        K L)).symm

private theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq :
    ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E E₂).range.toAddSubgroup := by
  change
    (finiteNormSubgroup rationalIdeleClassRepresentation
      L.field
      (smallHilbertFiniteGaloisNormNeighborhood K L).field
      (smallHilbertFiniteGaloisNormNeighborhood K L).below).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E E₂).range.toAddSubgroup
  exact
    (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      L.field
      (smallHilbertFiniteGaloisNormNeighborhood K L).field
      (smallHilbertFiniteGaloisNormNeighborhood K L).below
      (smallHilbertFiniteGaloisNormNeighborhood K L).normal)

/-- The abstract norm map lands directly in the ordinary norm range of the
chosen neighbourhood.  Composing the two named subgroup equalities here
keeps downstream membership proofs pointwise. -/
private theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq_ordinaryNormRange :
    ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom =
      (_root_.ideleClassNorm E N).range.toAddSubgroup :=
  (smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq K L).trans
    (congrArg Subgroup.toAddSubgroup
      (smallHilbertFiniteGaloisNormNeighborhood_ordinaryNormRange_eq K L).symm)

/-- Pointwise form of the combined norm-range equality. -/
theorem
    smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_mem_ordinaryNormRange
    (a : Additive (IdeleClassGroup E))
    (ha :
      a ∈ ((smallHilbertFiniteGaloisNormNeighborhood K L).normSubgroup
        rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field
            (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom) :
    a ∈ (_root_.ideleClassNorm E N).range.toAddSubgroup :=
  (le_of_eq
    (smallHilbertFiniteGaloisNormNeighborhood_abstractNormMap_eq_ordinaryNormRange
      K L)) ha


end RationalFixedField
end IdealClassFieldTheory
end GlobalClassFieldTheory
