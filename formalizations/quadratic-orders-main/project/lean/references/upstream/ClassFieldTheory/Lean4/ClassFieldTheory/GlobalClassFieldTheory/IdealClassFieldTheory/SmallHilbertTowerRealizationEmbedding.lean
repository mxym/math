/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealizationBase

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

/-- A controlled embedding of the concrete finite Galois norm
neighbourhood.  Its restriction to the middle field is the literal
inclusion of that fixed field in `SeparableClosure ℚ`. -/
noncomputable def
    smallHilbertNormNeighborhoodEmbedding :
    N →ₐ[ℚ] SeparableClosure ℚ :=
  (smallHilbertNormNeighborhoodAlignment K L).toAlgHom.comp
    (numberFieldSeparableClosureEmbedding N)

@[simp]
theorem smallHilbertNormNeighborhoodEmbedding_algebraMap
    (x : E) :
    smallHilbertNormNeighborhoodEmbedding K L
        (algebraMap E N x) =
      (x : SeparableClosure ℚ) := by
  change
    (smallHilbertNormNeighborhoodForwardAlignment K L).symm
        ((numberFieldSeparableClosureEmbedding N)
          (algebraMap E N x)) =
      (x : SeparableClosure ℚ)
  rw [← smallHilbertNormNeighborhoodForwardAlignment_apply K L x]
  exact
    (smallHilbertNormNeighborhoodForwardAlignment K L).symm_apply_apply _

private abbrev smallHilbertNormNeighborhoodEmbeddedBase :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (AlgHom.fieldRange
      ((smallHilbertNormNeighborhoodEmbedding K L).comp
        (smallHilbertTowerNormAmbientAlgHom K L)))

private abbrev smallHilbertNormNeighborhoodEmbeddedField :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (AlgHom.fieldRange
      (smallHilbertNormNeighborhoodEmbedding K L))

private theorem smallHilbertNormNeighborhoodEmbeddedField_le_base :
    (smallHilbertNormNeighborhoodEmbeddedField K L).toSubgroup ≤
      (smallHilbertNormNeighborhoodEmbeddedBase K L).toSubgroup := by
  change
    (AlgHom.fieldRange
        (smallHilbertNormNeighborhoodEmbedding K L)).fixingSubgroup ≤
      (AlgHom.fieldRange
        ((smallHilbertNormNeighborhoodEmbedding K L).comp
          (smallHilbertTowerNormAmbientAlgHom K L))).fixingSubgroup
  apply
    (AlgHom.fieldRange
      ((smallHilbertNormNeighborhoodEmbedding K L).comp
        (smallHilbertTowerNormAmbientAlgHom K L))).fixingSubgroup_le
  exact
    AlgHom.range_comp_le_range
      (smallHilbertTowerNormAmbientAlgHom K L)
      (smallHilbertNormNeighborhoodEmbedding K L)

theorem smallHilbertNormNeighborhoodEmbeddedBase_eq :
    smallHilbertNormNeighborhoodEmbeddedBase K L = L.field := by
  have hi :
      (smallHilbertNormNeighborhoodEmbedding K L).comp
          (smallHilbertTowerNormAmbientAlgHom K L) =
        (abstractFixedField ℚ (SeparableClosure ℚ) L.field).val := by
    apply AlgHom.ext
    intro x
    change smallHilbertNormNeighborhoodEmbedding K L
      (smallHilbertTowerNormAmbientAlgHom K L x) = (x : SeparableClosure ℚ)
    rw [smallHilbertTowerNormAmbientAlgHom_apply K L x]
    exact smallHilbertNormNeighborhoodEmbedding_algebraMap K L x
  change
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange
          ((smallHilbertNormNeighborhoodEmbedding K L).comp
            (smallHilbertTowerNormAmbientAlgHom K L))) =
      L.field
  rw [hi, IntermediateField.fieldRange_val]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) L.field

private noncomputable def
    smallHilbertNormNeighborhoodSeparableClosureEquiv :
    let j := smallHilbertNormNeighborhoodEmbedding K L
    let i := j.comp (smallHilbertTowerNormAmbientAlgHom K L)
    let : Algebra E (SeparableClosure ℚ) :=
      i.toRingHom.toAlgebra
    SeparableClosure E ≃ₐ[E] SeparableClosure ℚ := by
  intro j i alg
  let : @IsScalarTower ℚ E (SeparableClosure ℚ)
      (Algebra.toSMul (R := ℚ) (A := E))
      alg.toSMul
      (Algebra.toSMul (R := ℚ) (A := SeparableClosure ℚ)) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let : IsSepClosure E (SeparableClosure ℚ) :=
    ⟨IsSepClosure.sep_closed ℚ,
      Algebra.isSeparable_tower_top_of_isSeparable
        ℚ E (SeparableClosure ℚ)⟩
  exact
    IsSepClosure.equiv E
      (SeparableClosure E) (SeparableClosure ℚ)

/-- The finite Galois extension given by the embedded small Hilbert
norm-neighborhood field over the embedded intermediate field. -/
noncomputable def
    smallHilbertFiniteGaloisNormNeighborhoodRaw :
    FiniteGaloisSubextension
      (smallHilbertNormNeighborhoodEmbeddedBase K L) := by
  let : @IsScalarTower ℚ E N
      (Algebra.toSMul (R := ℚ) (A := E))
      (smallHilbertTowerNormAmbientSMul K L)
      (Algebra.toSMul (R := ℚ) (A := N)) :=
    smallHilbertTowerNormAmbientScalarTower K L
  let j : N →ₐ[ℚ] SeparableClosure ℚ :=
    smallHilbertNormNeighborhoodEmbedding K L
  let i : E →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ E N)
  let B : ClosedSubgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange
  let T : ClosedSubgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    smallHilbertNormNeighborhoodEmbeddedField K L
  have hTB : T.toSubgroup ≤ B.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    exact AlgHom.range_comp_le_range (IsScalarTower.toAlgHom ℚ E N) j
  let raw : FiniteGaloisSubextension B := {
    field := T
    below := hTB
    normal := ambientEmbeddedExtensionSubgroup_normal ℚ E N j
      (smallHilbertNormNeighborhoodSeparableClosureEquiv K L)
    finite := ambientEmbeddedExtensionQuotient_finite ℚ E N j
      (smallHilbertNormNeighborhoodSeparableClosureEquiv K L) }
  have hi : IsScalarTower.toAlgHom ℚ E N =
      smallHilbertTowerNormAmbientAlgHom K L := by
    apply AlgHom.ext
    intro x
    exact (IsScalarTower.toAlgHom_apply ℚ E N x).trans
      (smallHilbertTowerNormAmbientAlgHom_apply K L x).symm
  have hB : B = smallHilbertNormNeighborhoodEmbeddedBase K L :=
    congrArg
      (fun f : E →ₐ[ℚ] N =>
        closedFixingSubgroup ℚ (SeparableClosure ℚ) (j.comp f).fieldRange) hi
  exact hB ▸ raw


end RationalFixedField
end IdealClassFieldTheory
end GlobalClassFieldTheory
