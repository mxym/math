/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityTowerNorm


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

variable
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]

/-- Same-base norm-residue naturality in a compatible ambient:
restriction from the larger finite Galois subextension commutes with
the canonical projection between its finite norm quotient and the
norm quotient of an intermediate subextension. -/
theorem normResidueSymbol_restriction_sameBase
    (D : DegreeData G)
    (A : Rep ℤ G)
    (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G)
    (M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal :
      (CyclicCohomology.extensionSubgroup
        K.field L (hLM.trans hMK)).Normal]
    [hMnormal :
      (CyclicCohomology.extensionSubgroup K.field M hMK).Normal]
    [hLfinite :
      Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field L
            (hLM.trans hMK))] :
    letI _ : Finite
        (M.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite
        K.field M L hLM hMK
    letI hIntermediateFinite : Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field M hMK) :=
      abstractReciprocity_intermediateQuotient_finite
        K.field M L hLM hMK
    let EM : FiniteGaloisSubextension K.field :=
      ⟨M, hMK, hMnormal, hIntermediateFinite⟩
    let EL : FiniteGaloisSubextension K.field :=
      ⟨L, hLM.trans hMK, hLnormal, hLfinite⟩
    let hEL_EM : EL.field.toSubgroup ≤ EM.field.toSubgroup :=
      hLM
    let QL : Type :=
      FiniteNormQuotient A K.field L (hLM.trans hMK)
    let QM : Type :=
      FiniteNormQuotient A K.field M hMK
    let AL : Type :=
      Additive
        (Abelianization
          (K.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup
              K.field L (hLM.trans hMK)))
    let AM : Type :=
      Additive
        (Abelianization
          (K.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup K.field M hMK))
    let restriction :
        AL →+ AM :=
      MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedRestriction
          K.field K.field EM.field EL.field
          EM.below EL.below le_rfl hEL_EM)
    let projection :
        QL →+ QM :=
      abstractReciprocityNormProjection
        A K.field EM.field EL.field hEL_EM EM.below
    let normEL :
        QL →+ AL :=
      (DegreeData.normResidueSymbol
        (D := D) (A := A) (v := v) (hcf := hcf)
        (K := K) (L := EL)).toAddMonoidHom
    let normEM :
        QM →+ AM :=
      (DegreeData.normResidueSymbol
        (D := D) (A := A) (v := v) (hcf := hcf)
        (K := K) (L := EM)).toAddMonoidHom
    (restriction.comp normEL :
        QL →+ AM) =
      (normEM.comp projection :
        QL →+ AM) := by
  let _ : Finite
      (M.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite
      K.field M L hLM hMK
  let hIntermediateFinite : Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K.field M hMK) :=
    abstractReciprocity_intermediateQuotient_finite
      K.field M L hLM hMK
  let EM : FiniteGaloisSubextension K.field :=
    ⟨M, hMK, hMnormal, hIntermediateFinite⟩
  let EL : FiniteGaloisSubextension K.field :=
    ⟨L, hLM.trans hMK, hLnormal, hLfinite⟩
  let hEL_EM : EL.field.toSubgroup ≤ EM.field.toSubgroup :=
    hLM
  let QL : Type :=
    FiniteNormQuotient A K.field L (hLM.trans hMK)
  let QM : Type :=
    FiniteNormQuotient A K.field M hMK
  let AL : Type :=
    Additive
      (Abelianization
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field L (hLM.trans hMK)))
  let AM : Type :=
    Additive
      (Abelianization
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field M hMK))
  let restriction :
      AL →+ AM :=
    MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedRestriction
        K.field K.field EM.field EL.field
        EM.below EL.below le_rfl hEL_EM)
  let projection :
      QL →+ QM :=
    abstractReciprocityNormProjection
      A K.field EM.field EL.field hEL_EM EM.below
  let T : FiniteAbstractFieldExtension G :=
    { base := K
      field := K
      below := le_rfl
      finiteQuotient :=
        (FiniteGaloisSubextension.refl K.field).finite }
  have hnat :=
    D.normResidueNaturality_norm_restriction
      (hLnormal := hMnormal) (hL'normal := hLnormal)
      (hLKfinite := hIntermediateFinite) (hL'K'finite := hLfinite)
      A v hcf T M L hMK (hLM.trans hMK) hLM
  rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection]
    at hnat
  dsimp only [T, restriction, projection, EM, EL, hEL_EM, QL, QM, AL, AM,
    FiniteGaloisSubextension.extensionQuotient] at hnat ⊢
  exact hnat

end Reciprocity
end GlobalClassFieldTheory
