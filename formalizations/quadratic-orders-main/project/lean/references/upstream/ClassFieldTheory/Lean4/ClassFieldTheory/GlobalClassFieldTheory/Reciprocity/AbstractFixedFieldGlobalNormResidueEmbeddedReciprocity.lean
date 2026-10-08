/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidueNormClasses


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

section EmbeddedNumberFieldRealization

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]


attribute [local instance]
  numberFieldEmbeddedIdeleClassGroupIsMulCommutative
  numberFieldEmbeddedIdeleClassSubgroupNormal
  numberFieldEmbeddedExtensionSubgroupNormal
  numberFieldEmbeddedExtensionQuotientFinite
  numberFieldEmbeddedAbsoluteQuotientFinite
  numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
  numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
  numberFieldEmbeddedAbstractFixedFieldScalarTower
  numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  numberFieldEmbeddedAbstractFixedFieldNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra
  numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois

variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The abelianized quotient of the explicitly embedded tower is the
actual abelian Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
      (Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) ≃+
      Additive Gal(L / K) :=
  MulEquiv.toAdditive
    ((MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K L j)).trans
        (Abelianization.equivOfComm :
          Gal(L / K) ≃*
            Abelianization Gal(L / K)).symm)

/-- The actual global norm-residue equivalence constructed from an
explicit compatible embedding of a finite abelian number-field
extension into the rational separable closure. -/
noncomputable def globalNormResidueEquivOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive Gal(L / K) := by
  let eNorm :
      FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
        Additive
          (Abelianization
            (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      (numberFieldEmbeddedFiniteAbstractField K L j)
      (numberFieldEmbeddedFiniteGaloisSubextension K L j)
  exact
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j).symm.trans
      (eNorm.trans
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j))

/-- The explicit-embedding norm-residue equivalence on a finite norm class. -/
theorem globalNormResidueEquivOfEmbedding_finiteNormClass
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :
    globalNormResidueEquivOfEmbedding K L j
        (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K L j x) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j) x) := by
  simp only [globalNormResidueEquivOfEmbedding, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]

/-- The global norm-residue homomorphism obtained from an explicit
compatible embedding. -/
noncomputable def globalNormResidueMonoidHomOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Gal(L / K) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L / K) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquivOfEmbedding K L j)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the explicit-embedding global norm-residue map is
the abstract norm-residue symbol evaluated on the corresponding genuine
fixed-part finite norm class. -/
@[simp]
theorem globalNormResidueMonoidHomOfEmbedding_apply
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHomOfEmbedding K L j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L j)
            (numberFieldEmbeddedFiniteGaloisSubextension K L j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K L j (Additive.ofMul c))))) := by
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L j c
  change
    Additive.toMul
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j)
          ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
            K L j).symm
            (Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range c))))) =
      _
  rw [← hclass,
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
      K L j).symm_apply_apply]

omit [FiniteDimensional K L] [IsAbelianGalois K L] in


theorem numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard :
    numberFieldTowerIdeleClassEquivAmbientFixed K L =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
        (numberFieldSeparableClosureEmbedding L) := by
  let j := numberFieldSeparableClosureEmbedding L
  have hBase :
      numberFieldTowerAbstractBaseFieldEquiv K L =
        numberFieldEmbeddedAbstractBaseFieldEquiv K L j := by
    rfl
  unfold numberFieldTowerIdeleClassEquivAmbientFixed
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
  rw [hBase]
  dsimp only
  congr 1

/- At the chosen embedding, both constructions use the same fixed tower and
abstract reciprocity data.  We compare their values on the particular fixed
idele class needed below; the two implementations of the finite norm-quotient
equivalence are deliberately not compared as dependent structures. -/
private theorem numberFieldTowerNormResidueValue_eq_embedded_standard
    (c : IdeleClassGroup K) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L)
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
            (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c)))) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L (numberFieldSeparableClosureEmbedding L)
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L
            (numberFieldSeparableClosureEmbedding L))
          (numberFieldEmbeddedFiniteGaloisSubextension K L
            (numberFieldSeparableClosureEmbedding L))
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldEmbeddedBaseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
              (numberFieldSeparableClosureEmbedding L) (Additive.ofMul c)))) := by
  have hIdeleClassEquiv :
      numberFieldTowerIdeleClassEquivAmbientFixed K L =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
          (numberFieldSeparableClosureEmbedding L) := by
    exact numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard K L
  have hFiniteAbstractField :
      numberFieldTowerReciprocityFiniteAbstractField K L =
        numberFieldEmbeddedFiniteAbstractField K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hSubextension :
      numberFieldTowerFiniteGaloisSubextension K L =
        numberFieldEmbeddedFiniteGaloisSubextension K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hGaloisComparison :
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L =
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L (numberFieldSeparableClosureEmbedding L) := by
    rfl
  simp only [← hGaloisComparison]
  cases hFiniteAbstractField
  cases hSubextension
  rw [← hIdeleClassEquiv]
  rfl

/-- At the standard embedding, the two global norm-residue equivalences
agree on the actual norm quotient.  The comparison is extensional: it uses
surjectivity of the quotient map and the established evaluation formulas,
not definitional equality of the two quotient constructions. -/
theorem globalNormResidueEquiv_eq_ofEmbedding_standard :
    globalNormResidueEquiv K L =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply AddEquiv.ext
  intro q
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective
      (_root_.ideleClassNorm K L).range (Additive.toMul q)
  have hq :
      Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c) = q :=
    Additive.toMul.injective hc
  rw [← hq]
  have hTower :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  have hEmbedded :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L (numberFieldSeparableClosureEmbedding L) c
  conv_lhs =>
    rw [← hTower, globalNormResidueEquiv_finiteNormClass]
  conv_rhs =>
    rw [← hEmbedded, globalNormResidueEquivOfEmbedding_finiteNormClass]
  exact numberFieldTowerNormResidueValue_eq_embedded_standard K L c

/-- The existing global norm-residue map is the explicit-embedding
construction for the standard chosen embedding of the top field. -/
theorem globalNormResidueMonoidHom_eq_ofEmbedding_standard :
    globalNormResidueMonoidHom K L =
      globalNormResidueMonoidHomOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply MonoidHom.ext
  intro c
  apply Additive.toMul.injective
  change
    globalNormResidueEquiv K L
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)) =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L)
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c))
  exact congrArg
    (fun e :
      Additive
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) ≃+
        Additive (Gal(L / K)) =>
      e (Additive.ofMul
        (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)))
    (globalNormResidueEquiv_eq_ofEmbedding_standard K L)

end EmbeddedNumberFieldRealization

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

/-- A compatible common embedding reverses the inclusion of the two base
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedBaseSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    (numberFieldEmbeddedLowerEmbedding K' L' j).fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨algebraMap K K' y, ?_⟩
  change
    j (algebraMap K' L' (algebraMap K K' y)) =
      j (algebraMap L L' (algebraMap K L y))
  rw [← IsScalarTower.algebraMap_apply K K' L',
    ← IsScalarTower.algebraMap_apply K L L']

omit [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L']
    [IsScalarTower K K' L'] [IsScalarTower K L L'] in
/-- A compatible common embedding reverses the inclusion of the two top
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedTopSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedTopSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedTopSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    j.fieldRange.fixingSubgroup ≤
      (j.comp
        (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup
  apply
    (j.comp
      (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap L L' y, rfl⟩

end EmbeddedNumberFieldRestriction

end Reciprocity
end GlobalClassFieldTheory
