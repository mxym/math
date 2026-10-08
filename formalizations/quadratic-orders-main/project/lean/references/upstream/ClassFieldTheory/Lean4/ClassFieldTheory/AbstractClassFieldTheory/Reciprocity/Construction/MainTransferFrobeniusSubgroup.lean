/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.DoubleCosetOrbitGeometry


set_option autoImplicit false


universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology
open CategoryTheory

noncomputable section

open scoped BigOperators
open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The absolute group of an intermediate field, identified with its
literal copy inside the absolute group of the base field. -/
noncomputable def transferNormNaturalityIntermediateAbsoluteEquiv
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    K'.toSubgroup ≃* extensionSubgroup K K' hK'K :=
  MulEquiv.ofBijective
    ((Subgroup.inclusion hK'K).codRestrict
      (extensionSubgroup K K' hK'K) (fun k' => k'.2))
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h), by
      rintro ⟨k, hk'⟩
      let k' : K'.toSubgroup := ⟨k.1, hk'⟩
      exact ⟨k', Subtype.ext rfl⟩⟩

/-- The absolute intermediate-field equivalence evaluates by the underlying transfer map. -/
@[simp]
theorem transferNormNaturalityIntermediateAbsoluteEquiv_apply
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (k' : K'.toSubgroup) :
    ((transferNormNaturalityIntermediateAbsoluteEquiv K K' hK'K k').1 : G) = k'.1 :=
  rfl

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal] :
    (extensionSubgroup K' L hLK').Normal := by
  have hcomap : extensionSubgroup K' L hLK' =
      (extensionSubgroup K L (hLK'.trans hK'K)).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, mem_extensionSubgroup_iff,
      mem_extensionSubgroup_iff]
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData

/-- The restriction map on the infinite Frobenius quotients is injective
when the top field is unchanged. -/
theorem transferNormNaturalityFrobeniusTowerMap_injective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Injective
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  have hmem :
      (Subgroup.inclusion E.below k')⁻¹ * Subgroup.inclusion E.below l' ∈
        D.extensionInertiaWithin E.base.field L (hL.trans E.below) :=
    QuotientGroup.eq.mp h
  constructor
  · apply (mem_extensionSubgroup_iff E.field.field L hL (k'⁻¹ * l')).2
    have hG := (mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below)
      ((Subgroup.inclusion E.below k')⁻¹ *
        Subgroup.inclusion E.below l')).1 hmem.1
    simpa using hG
  · have hI := hmem.2
    change D.degree (((Subgroup.inclusion E.below k')⁻¹ *
      Subgroup.inclusion E.below l' : E.base.field.toSubgroup) : G) = 1 at hI
    change D.degree ((k'⁻¹ * l' : E.field.field.toSubgroup) : G) = 1
    exact hI

/-- The copy of `G(\widetilde L/K')` inside
`G(\widetilde L/K)`.  This is the subgroup `H` used in the classical
double-coset proof of transfer--norm naturality. -/
def transferNormNaturalityFrobeniusIntermediateSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Subgroup (E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :=
  (D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl).range

/-- The subgroup above is also the image of `G_K'` under the quotient
projection `G_K → G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL =
      (extensionSubgroup E.base.field E.field.field E.below).map
        (QuotientGroup.mk'
          (D.extensionInertiaWithin E.base.field L
            (hL.trans E.below))) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨Subgroup.inclusion E.below k', ?_, rfl⟩
    exact k'.2
  · rintro ⟨k, hk', rfl⟩
    let k' : E.field.field.toSubgroup := ⟨k.1, hk'⟩
    refine ⟨QuotientGroup.mk k', ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion E.below k') =
      QuotientGroup.mk k
    rfl

/-- Quotient projection maps the literal absolute subgroup belonging to
`K'` onto its copy `H` inside `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityIntermediateToFrobeniusSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    extensionSubgroup E.base.field E.field.field E.below →*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  refine ((QuotientGroup.mk'
    (D.extensionInertiaWithin E.base.field L (hL.trans E.below))).comp
      (extensionSubgroup E.base.field E.field.field E.below).subtype).codRestrict
        (D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL) ?_
  intro m
  change QuotientGroup.mk m.1 ∈
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  exact ⟨m.1, m.2, rfl⟩

/-- The map from the intermediate quotient onto the Frobenius subgroup is surjective. -/
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Surjective
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL) := by
  intro h
  have hh : h.1 ∈
      (extensionSubgroup E.base.field E.field.field E.below).map
      (QuotientGroup.mk'
        (D.extensionInertiaWithin E.base.field L (hL.trans E.below))) := by
    rw [← D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
      E L hL]
    exact h.2
  obtain ⟨m, hm, hval⟩ := hh
  refine ⟨⟨m, hm⟩, ?_⟩
  apply Subtype.ext
  unfold transferNormNaturalityIntermediateToFrobeniusSubgroup
  simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hval

/-- The intermediate-to-Frobenius map has the stated value on each representative. -/
@[simp]
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_apply
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (m : extensionSubgroup E.base.field E.field.field E.below) :
    (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
      E L hL m).1 =
        (QuotientGroup.mk m.1 : E.base.field.toSubgroup ⧸
          D.extensionInertiaWithin E.base.field L (hL.trans E.below)) := by
  rfl

/-- The canonical coset equivalence from `G_K/G_Σ` to
`G(\widetilde L/K)/Γ` intertwines the two copies of the `K'`-action. -/
theorem frobeniusFixedCosetClosureEquiv_equivariant
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (m : extensionSubgroup E.base.field E.field.field E.below)
    (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ)) :
    D.frobeniusFixedCosetClosureEquiv E.base L (hL.trans E.below) σ (m • x) =
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m) •
        D.frobeniusFixedCosetClosureEquiv E.base L
          (hL.trans E.below) σ x := by
  refine Quotient.inductionOn' x ?_
  intro k
  change QuotientGroup.mk (QuotientGroup.mk (m.1 * k)) =
    QuotientGroup.mk
      ((D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m).1 * QuotientGroup.mk k)
  rw [D.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply]
  rfl


end DegreeData
end transferFrobeniusGeometry
end
end ClassFormation
