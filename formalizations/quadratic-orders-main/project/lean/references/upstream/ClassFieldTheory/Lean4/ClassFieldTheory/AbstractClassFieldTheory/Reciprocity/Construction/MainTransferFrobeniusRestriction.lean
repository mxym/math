/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusSubgroup


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


namespace DegreeData

/-- Restriction from the infinite Frobenius quotient onto the finite
Galois quotient is surjective. -/
theorem transferNormNaturalityExtensionRestriction_surjective
    (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Function.Surjective (D.extensionRestriction K L hLK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩


theorem transferNormNaturalityExtensionRestriction_ker_le_intermediate
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (D.extensionRestriction E.base.field L (hL.trans E.below)).ker ≤
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  intro q hq
  revert hq
  refine QuotientGroup.induction_on q ?_
  intro k hk
  change D.extensionRestriction E.base.field L (hL.trans E.below)
      (QuotientGroup.mk k) = 1 at hk
  rw [D.extensionRestriction_mk] at hk
  have hkL : k ∈
      extensionSubgroup E.base.field L (hL.trans E.below) := by
    exact QuotientGroup.eq_one_iff k |>.1 hk
  have hkK' : k ∈
      extensionSubgroup E.base.field E.field.field E.below := by
    apply (mem_extensionSubgroup_iff
      E.base.field E.field.field E.below k).2
    exact hL ((mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below) k).1 hkL)
  exact ⟨k, hkK', rfl⟩

/-- `H` has finite index in `G(\widetilde L/K)`, with no normality
assumption on the intermediate extension `K'/K`. -/
theorem transferNormNaturalityFrobeniusIntermediateFiniteIndex
    (D : DegreeData G) [IsTopologicalGroup G]
    (R : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ R.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup R.base.field L (hL.trans R.below)).Normal]
    [hL'normal : (extensionSubgroup R.field.field L hL).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup R L hL).FiniteIndex := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    R L hL]
  let I := D.extensionInertiaWithin R.base.field L (hL.trans R.below)
  let M := extensionSubgroup R.base.field R.field.field R.below
  have hIM : I ≤ M := by
    intro k hk
    apply (mem_extensionSubgroup_iff
      R.base.field R.field.field R.below k).2
    exact hL ((mem_extensionSubgroup_iff R.base.field L
      (hL.trans R.below) k).1 hk.1)
  let p := QuotientGroup.mk' I
  have hker : p.ker ≤ M := by
    simpa [p] using hIM
  let : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff,
    M.index_map_eq (QuotientGroup.mk'_surjective I) hker]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The copy of `G(\widetilde L/K')` is closed in
`G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediate_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    IsClosed (D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL : Set
        (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below))) := by
  let : CompactSpace E.field.field.toSubgroup :=
    isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
  let : IsClosed
      (D.extensionInertiaWithin E.field.field L hL :
        Set E.field.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.field L hL
  let : IsClosed (D.extensionInertiaWithin E.base.field L
      (hL.trans E.below) : Set E.base.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  change IsClosed (Set.range f)
  have hrange : Set.range f = Set.range f.toContinuousMap := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
  rw [hrange]
  simpa only [Set.image_univ] using
    (isCompact_univ.image f.continuous).isClosed


end DegreeData
end transferFrobeniusGeometry
end
end ClassFormation
