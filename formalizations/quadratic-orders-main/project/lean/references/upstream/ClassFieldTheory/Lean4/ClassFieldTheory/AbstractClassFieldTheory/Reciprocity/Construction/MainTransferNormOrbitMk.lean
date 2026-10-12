/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferNormOrbitEquiv


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

/-- The transfer-norm orbit equivalence sends quotient representatives to their norm orbits. -/
@[simp]
theorem transferNormNaturalityTransferNormOrbitEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (k : E.base.field.toSubgroup) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
        (Quotient.mk'' (QuotientGroup.mk
          (QuotientGroup.mk k : E.base.field.toSubgroup ⧸
            D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
          (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸
              D.transferNormNaturalityFrobeniusIntermediateSubgroup
                E L hL)) =
      Quotient.mk'' (QuotientGroup.mk k⁻¹ :
        E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ)) := by
  unfold transferNormNaturalityTransferNormOrbitEquiv
  simp only [Equiv.trans_apply, orbitQuotientSwapEquiv_mk,
    orbitQuotientClosedCyclicEquiv_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_symm_mk,
    Subgroup.quotientEquivOfEq_mk]
  apply congrArg Quotient.mk''
  exact (D.frobeniusFixedCosetClosureEquiv E.base L
    (hL.trans E.below) σ).symm_apply_apply (QuotientGroup.mk k⁻¹)


end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
