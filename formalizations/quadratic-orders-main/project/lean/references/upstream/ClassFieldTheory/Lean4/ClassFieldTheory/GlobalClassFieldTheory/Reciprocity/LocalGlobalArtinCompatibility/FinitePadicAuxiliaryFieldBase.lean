/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

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

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra

local instance finitePadicAuxiliaryExtensionNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

local instance finitePadicAuxiliaryExtensionQuotientFinite :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L

noncomputable local instance finitePadicAuxiliaryExtensionQuotientIsMulCommutative :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm
                (e x) (e y)⟩ }

/-- The concrete auxiliary fixed field attached to a simultaneous
finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IntermediateField ℚ (SeparableClosure ℚ) := by
  exact
    IntermediateField.fixedField
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup

/-- A nonzero-degree lift produces a genuine number field: its
concrete fixed field is finite over `ℚ`. -/
theorem numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteDimensional ℚ
      (numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ) := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  apply
    (InfiniteGalois.isOpen_iff_finite
      (K := SeparableClosure ℚ) F).1
  change IsOpen
    (IntermediateField.fixedField S.toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField S]
  exact
    numberFieldTowerFinitePadicCyclicFixedSubgroup_isOpen
      (K := K) (L := L) p τ hτ

/-- The compatible embedded copy of `K` lies in every auxiliary
cyclic fixed field. -/
theorem numberFieldTowerBaseField_le_finitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    numberFieldTowerBaseField K L ≤
      numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ := by
  intro x hx
  change x ∈ IntermediateField.fixedField
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change
    σ ∈
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup at hσ
  obtain ⟨u, hu, rfl⟩ := hσ
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldTowerBaseField K L) u.1).1 u.2 x hx

/-- The compatible embedding of the original base field into the
genuine auxiliary fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    K →ₐ[ℚ]
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  exact
    (numberFieldTowerLowerEmbedding K L).codRestrict F.toSubalgebra
      (fun x =>
        numberFieldTowerBaseField_le_finitePadicCyclicFixedField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary base embedding recovers the fixed lower embedding
into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) =
        numberFieldTowerLowerEmbedding K L x := by
  rfl

/-- The compatible copy of the original top field lies in the
auxiliary compositum fixed field. -/
theorem numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    {x : SeparableClosure ℚ}
    (hx : x ∈ numberFieldInRationalSeparableClosure L) :
    x ∈
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  change x ∈ IntermediateField.fixedField
    (S.toSubgroup ⊓ T.toSubgroup)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσT : σ ∈ T.toSubgroup :=
    hσ.2
  change
    σ ∈
      (numberFieldInRationalSeparableClosure L).fixingSubgroup
        at hσT
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldInRationalSeparableClosure L) σ).1
      hσT x hx

/-- The compatible embedding of the original top field into the
auxiliary compositum fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryTopEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    L →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  exact
    (numberFieldSeparableClosureEmbedding L).codRestrict
      (E.restrictScalars ℚ).toSubalgebra
      (fun x =>
        numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary top embedding recovers the chosen top-field
embedding into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : L) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        numberFieldSeparableClosureEmbedding L x := by
  rfl

/-- The compatible base and top embeddings form the actual
base-change square inside the rational separable closure. -/
theorem numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ (algebraMap K L x) :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) := by
  rfl

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_baseRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_topRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp
      (IsScalarTower.toAlgHom ℚ K L)).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

instance
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ))
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact
    numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
      (K := K) (L := L) p τ x

/-- The genuine auxiliary fixed field is Galois over the original
base field through the compatible embedding above. -/
theorem numberFieldTowerFinitePadicAuxiliaryBase_isGalois
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsGalois K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let hSH :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  let B :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let FB :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH
  let auxiliaryBaseAlgebra : Algebra B FB :=
    (LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH).algebra
  let auxiliaryBaseGalois : IsGalois B FB :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H S hSH
      (numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
        (K := K) (L := L) p τ)
  let eK :=
    numberFieldTowerAbstractBaseFieldEquiv K L
  refine
    @IsGalois.of_equiv_equiv
      B FB _ _ auxiliaryBaseAlgebra
      K F _ _
      (numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ)
      auxiliaryBaseGalois
      eK.symm.toRingEquiv (RingEquiv.refl F) ?_
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change
    ((eK (eK.symm x) : B) : SeparableClosure ℚ) =
      (x : SeparableClosure ℚ)
  exact
    congrArg Subtype.val (eK.apply_symm_apply x)


end Reciprocity
end GlobalClassFieldTheory
