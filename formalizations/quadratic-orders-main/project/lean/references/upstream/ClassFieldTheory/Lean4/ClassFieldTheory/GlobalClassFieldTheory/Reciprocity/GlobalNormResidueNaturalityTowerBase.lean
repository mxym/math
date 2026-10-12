/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityFixedComparison


set_option autoImplicit false


open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u


attribute [local instance]
  naturalityIdeleClassCommGroup
  ideleClassGroupIsMulCommutative
  ideleClassSubgroupNormal

section EmbeddedNumberFieldRestriction

variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']


/-- Rebracketing the compatible tower does not change its embedded lower
fixing subgroup. -/
private theorem numberFieldEmbeddedBaseSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
  have hi :
      numberFieldEmbeddedLowerEmbedding K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j) =
        numberFieldEmbeddedLowerEmbedding K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
    ext x
    simp only [numberFieldEmbeddedLowerEmbedding, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  simp only [numberFieldEmbeddedBaseSubgroup, hi]

omit [Field K] [NumberField K]
    [Algebra K K'] [Algebra K L'] [IsScalarTower K K' L'] in
/-- The top subgroup of the rebracketed base-change tower is the embedded
fixing subgroup of the intermediate field. -/
private theorem numberFieldEmbeddedTopSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K' L' j := by
  rfl

/-- Reidentify the two presentations of the embedded lower fixing subgroup
without transporting dependent subgroup data through an equality. -/
private noncomputable def numberFieldEmbeddedBaseChangeBaseEquiv
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ≃*
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup :=
  MulEquiv.subgroupCongr
    (congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedBaseSubgroup_baseChange_eq K K' L L' j))

/-- Under the identity equivalence of the two lower fixing subgroups, the
relative subgroup for the base change is exactly the target presentation. -/
private theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))).map
          (numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j).toMonoidHom =
      CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))
        (numberFieldEmbeddedBaseSubgroup K' L' j)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hTop :
      (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup =
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup :=
    congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedTopSubgroup_baseChange_eq
        (K := K) (K' := K') (L' := L') j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change
      ((e y :
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_apply, ← hTop]
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change
      (((e.symm x :
          (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup)
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_symm_apply, hTop]
    exact hx

/-- Normality of the relative subgroup between the two embedded base fields
in a finite Galois base change. -/
private theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_normal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hNormal :=
    (numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)).map
        e.toMonoidHom e.surjective
  rw [numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    K K' L L' j] at hNormal
  exact hNormal

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal :=
  numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j

/-- Finiteness of the relative quotient between the two embedded base fields
in a finite Galois base change. -/
private theorem numberFieldEmbeddedBaseChangeExtensionQuotient_finite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  let N :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
  let M :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
  let hNNormal : N.Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  let hMNormal : M.Normal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j
  let hNFinite :
      Finite
        ((numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) :=
    numberFieldEmbeddedExtensionQuotient_finite K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  have hmap : N.map e.toMonoidHom = M :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq K K' L L' j
  have hle : N ≤ M.comap e.toMonoidHom := by
    rw [← hmap]
    exact Subgroup.le_comap_map e.toMonoidHom N
  let f :
      ((numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) →*
        ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.map N M e.toMonoidHom hle
  have hmk : Function.Surjective
      (QuotientGroup.mk ∘ e :
        (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup →
          (numberFieldEmbeddedBaseSubgroup K L
              (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.mk_surjective.comp e.surjective
  have hsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective
      (N := N) M e.toMonoidHom hmk hle
  exact Finite.of_surjective f hsurj

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  numberFieldEmbeddedBaseChangeExtensionQuotient_finite K K' L L' j

/-- Reuse the canonical absolute fixed-field witness for the lower embedded
tower.  The base-change relative witness below needs this exact instance path
when forming the absolute finite-dimensional tower. -/
noncomputable local instance
    numberFieldEmbeddedBaseChangeBaseFixedFieldFiniteDimensional
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))) :=
  numberFieldEmbeddedAbstractFixedFieldFiniteDimensional K L
    (j.comp (IsScalarTower.toAlgHom ℚ L L'))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j)

local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldScalarTower
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldIsGalois
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j)


end EmbeddedNumberFieldRestriction

end Reciprocity
end GlobalClassFieldTheory
