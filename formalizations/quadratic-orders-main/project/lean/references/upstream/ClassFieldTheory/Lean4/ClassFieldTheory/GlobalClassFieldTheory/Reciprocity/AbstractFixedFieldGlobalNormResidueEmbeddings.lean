/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue


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

/-- The algebra structure on the rational separable closure induced by a
specified rational field embedding.  It is deliberately not an instance:
different embeddings of the same field need not induce definitionally equal
algebra structures. -/
@[reducible]
noncomputable def rationalEmbeddingSeparableClosureAlgebra
    {F : Type} [Field F] [Algebra ℚ F]
    (i : F →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra F (SeparableClosure ℚ) :=
  i.toRingHom.toAlgebra

/-- Two rational embeddings of the same number field into the fixed
rational separable closure differ by an automorphism of that
separable closure. -/
theorem exists_numberFieldEmbeddingComparisonAutomorphism
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    ∃ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
      ∀ x : F, σ (i x) = j x := by
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    rationalEmbeddingSeparableClosureAlgebra i
  let hScalarTower : IsScalarTower ℚ F (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let hSeparable : Algebra.IsSeparable F (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ F (SeparableClosure ℚ)
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := ℚ) (L := F)
      (M := SeparableClosure ℚ)
      (E := SeparableClosure ℚ)) j
  let σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id ℚ (SeparableClosure ℚ))).1
  refine ⟨σ, ?_⟩
  intro x
  have hx :=
    congrArg (fun ψ : F →ₐ[ℚ] SeparableClosure ℚ => ψ x) hφ
  exact hx

/-- The canonical comparison automorphism between two rational
embeddings of one number field into the fixed separable closure. -/
noncomputable def numberFieldEmbeddingComparisonAutomorphism
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (exists_numberFieldEmbeddingComparisonAutomorphism i j)

/-- The comparison automorphism carries the first embedded copy of the
number field to the second one pointwise. -/
@[simp]
theorem numberFieldEmbeddingComparisonAutomorphism_apply
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ)
    (x : F) :
    numberFieldEmbeddingComparisonAutomorphism i j (i x) =
      j x :=
  Classical.choose_spec
    (exists_numberFieldEmbeddingComparisonAutomorphism i j) x

/-- Conjugating the fixing subgroup of one embedded copy of a number
field by the comparison automorphism gives the fixing subgroup of the
other embedded copy. -/
theorem conjugateClosedFixingSubgroup_embeddingRange
    {F : Type} [Field F] [NumberField F]
    (i j : F →ₐ[ℚ] SeparableClosure ℚ) :
    conjugateClosedSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) i.fieldRange)
        (numberFieldEmbeddingComparisonAutomorphism j i) =
      RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) j.fieldRange := by
  let s :=
    numberFieldEmbeddingComparisonAutomorphism j i
  ext τ
  change
    τ ∈ conjugateClosedSubgroup
        (closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange) s ↔
      τ ∈ closedFixingSubgroup ℚ (SeparableClosure ℚ) j.fieldRange
  rw [conjugateClosedSubgroup_mem]
  change
    s * τ * s⁻¹ ∈ i.fieldRange.fixingSubgroup ↔
      τ ∈ j.fieldRange.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    rcases hx with ⟨y, rfl⟩
    have hi := h (i y) ⟨y, rfl⟩
    have hs :
        s (j y) = i y :=
      numberFieldEmbeddingComparisonAutomorphism_apply j i y
    change s (τ (s.symm (i y))) = i y at hi
    have hpre : s.symm (i y) = j y := by
      rw [← hs, s.symm_apply_apply]
    rw [hpre, ← hs] at hi
    exact s.injective hi
  · intro h x hx
    rcases hx with ⟨y, rfl⟩
    have hj := h (j y) ⟨y, rfl⟩
    have hs :
        s (j y) = i y :=
      numberFieldEmbeddingComparisonAutomorphism_apply j i y
    change s (τ (s.symm (i y))) = i y
    have hpre : s.symm (i y) = j y := by
      rw [← hs, s.symm_apply_apply]
    rw [hpre, hj, hs]

section EmbeddedNumberFieldRealization

local instance numberFieldEmbeddedIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance numberFieldEmbeddedIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The lower embedding obtained by restricting an explicitly supplied
embedding of the top field into the rational separable closure. -/
noncomputable def numberFieldEmbeddedLowerEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  j.comp (IsScalarTower.toAlgHom ℚ K L)

/-- The exact algebra structure on the rational separable closure induced by
the lower embedding of an explicitly embedded number-field tower.  Keeping
this as a reducible definition lets every use of the associated separable-
closure equivalence share one definitionally identical algebra structure. -/
@[reducible]
noncomputable def numberFieldEmbeddedSeparableClosureAlgebra
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra K (SeparableClosure ℚ) :=
  rationalEmbeddingSeparableClosureAlgebra
    (numberFieldEmbeddedLowerEmbedding K L j)

/-- The fixing subgroup of the explicitly embedded lower field. -/
abbrev numberFieldEmbeddedBaseSubgroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedLowerEmbedding K L j).fieldRange

/-- The fixing subgroup of the explicitly embedded top field. -/
abbrev numberFieldEmbeddedTopSubgroup
    (_K L : Type) [Field L] [NumberField L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ) j.fieldRange

/-- The top fixing subgroup lies in the lower fixing subgroup. -/
theorem numberFieldEmbeddedTopSubgroup_le_baseSubgroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedTopSubgroup K L j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K L j).toSubgroup := by
  change
    j.fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K L j).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K L j).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap K L y, rfl⟩

/-- The separable closure of the actual lower field, identified with
the rational separable closure carrying the algebra structure induced
by an explicit compatible embedding. -/
noncomputable def numberFieldEmbeddedSeparableClosureEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra K L j
    SeparableClosure K ≃ₐ[K] SeparableClosure ℚ := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  letI hScalarTower : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq'
      (numberFieldEmbeddedLowerEmbedding K L j).comp_algebraMap.symm
  letI hseparable : Algebra.IsSeparable K (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ K (SeparableClosure ℚ)
  letI hSepClosure : IsSepClosure K (SeparableClosure ℚ) :=
    ⟨IsSepClosure.sep_closed ℚ, hseparable⟩
  exact
    IsSepClosure.equiv K
      (SeparableClosure K) (SeparableClosure ℚ)

/-- The relative subgroup arising from an explicit compatible
number-field embedding is normal. -/
theorem numberFieldEmbeddedExtensionSubgroup_normal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    (CyclicCohomology.extensionSubgroup
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange i))
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange j)) _).Normal
  exact ambientEmbeddedExtensionSubgroup_normal ℚ K L j e

/-- The normality witness for an explicitly embedded tower, registered at
the precise subgroup used by the downstream quotient constructions. -/
noncomputable local instance
    numberFieldEmbeddedExtensionSubgroupNormal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal :=
  numberFieldEmbeddedExtensionSubgroup_normal K L j

/-- The relative quotient arising from an explicit compatible
number-field embedding is finite. -/
theorem numberFieldEmbeddedExtensionQuotient_finite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    Finite
      ((closedFixingSubgroup ℚ (SeparableClosure ℚ)
          (AlgHom.fieldRange i)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange i))
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange j)) _)
  exact ambientEmbeddedExtensionQuotient_finite ℚ K L j e

/-- The relative-index witness for an explicitly embedded tower, registered
at the exact quotient consumed by `FiniteNormQuotient`. -/
noncomputable local instance
    numberFieldEmbeddedExtensionQuotientFinite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  numberFieldEmbeddedExtensionQuotient_finite K L j

/-- The finite abstract field determined by the lower member of an
explicitly embedded number-field tower. -/
noncomputable abbrev numberFieldEmbeddedFiniteAbstractField
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldEmbeddedBaseSubgroup K L j
  finite := by
    simpa only [numberFieldEmbeddedBaseSubgroup] using
      (ambientEmbeddedAbsoluteQuotientFinite
        ℚ K (numberFieldEmbeddedLowerEmbedding K L j))

/-- The absolute-index witness for the lower member of an explicitly embedded
tower, registered at its specialized quotient type. -/
noncomputable local instance
    numberFieldEmbeddedAbsoluteQuotientFinite
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (numberFieldEmbeddedBaseSubgroup K L j)
          (le_baseField
            (numberFieldEmbeddedBaseSubgroup K L j))) :=
  (numberFieldEmbeddedFiniteAbstractField K L j).finite

/-- The finite Galois subextension determined by an explicitly embedded
number-field tower. -/
noncomputable abbrev numberFieldEmbeddedFiniteGaloisSubextension
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteGaloisSubextension
      (numberFieldEmbeddedBaseSubgroup K L j) where
  field := numberFieldEmbeddedTopSubgroup K L j
  below := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  normal := numberFieldEmbeddedExtensionSubgroup_normal K L j
  finite := numberFieldEmbeddedExtensionQuotient_finite K L j

/-- Shared finite-dimensional data for the fixed field of the lower subgroup
in an explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)

/-- Shared relative finite-dimensional data for the two fixed fields of an
explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)
    (numberFieldEmbeddedExtensionQuotientFinite K L j)

local instance numberFieldEmbeddedAbstractFixedFieldScalarTower
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldNumberField
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) := by
  change FiniteDimensional ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))
  infer_instance

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  NumberField.of_module_finite ℚ _

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))).toRingHom.toAlgebra

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedExtensionSubgroupNormal K L j)

/-- The quotient of the two explicitly embedded fixing subgroups is
the actual relative Galois group. -/
noncomputable def
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient ≃*
      Gal(L / K) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  letI hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  let H₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap K L y, rfl⟩
  letI : (CyclicCohomology.extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal ℚ K L j e
  change
    (H₀.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H₀ J₀ hJH) ≃*
      Gal(L / K)
  exact ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ K L j e

/-- The original lower field is canonically equivalent to the fixed
field of its explicitly embedded fixing subgroup. -/
noncomputable def numberFieldEmbeddedAbstractBaseFieldEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    K ≃ₐ[ℚ]
      abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j) :=
  (numberFieldEmbeddedLowerEmbedding K L j).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (numberFieldEmbeddedLowerEmbedding K L j).fieldRange).symm)

/-- The original top field is canonically equivalent to the relative
fixed field of its explicitly embedded fixing subgroup. -/
noncomputable def numberFieldEmbeddedAbstractTopFieldEquiv
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    L ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup
          K L j)).restrictScalars ℚ :=
  j.equivFieldRange.trans
    (IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup j.fieldRange).symm)

/-- The two explicit fixed-field equivalences commute with the tower
algebra maps. -/
@[simp]
theorem numberFieldEmbeddedAbstractFieldEquiv_algebraMap
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (x : K) :
    numberFieldEmbeddedAbstractTopFieldEquiv K L j
        (algebraMap K L x) =
      algebraMap
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup K L j))
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j x) := by
  apply Subtype.ext
  rfl

/-- The ordinary idele class group of the explicitly embedded lower
field, transported to the fixed part of the rational absolute
idele-class representation. -/
noncomputable def numberFieldEmbeddedIdeleClassEquivAmbientFixed
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive (IdeleClassGroup K) ≃+
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j))).trans
      (rationalAbstractFixedFieldIdeleClassEquivFixed H)

/-- The abstract finite norm quotient of an explicitly embedded tower
is its genuine ordinary idele-class norm quotient. -/
noncomputable def
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    fixedFieldEquiv.trans
      (MulEquiv.toAdditive actualFieldEquiv.symm)


end EmbeddedNumberFieldRealization
end Reciprocity
end GlobalClassFieldTheory
