/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferNormOrbitMk


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

/-- On the classical chosen transfer representative `t`, the preceding
equivalence is literally the norm orbit represented by `t⁻¹`. -/
theorem transferNormNaturalityTransferNormOrbitEquiv_apply
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ q =
      Quotient.mk'' (QuotientGroup.mk (Quotient.out q.out.out)⁻¹ :
        E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ)) := by
  let orbitEquiv := D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  calc
    orbitEquiv q = orbitEquiv (Quotient.mk'' q.out) :=
      congrArg orbitEquiv (Quotient.out_eq' q).symm
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk q.out.out)) :=
      congrArg orbitEquiv (congrArg Quotient.mk'' (Quotient.out_eq' q.out).symm)
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk
        (QuotientGroup.mk (Quotient.out q.out.out)))) :=
      congrArg orbitEquiv (congrArg Quotient.mk''
        (congrArg QuotientGroup.mk (Quotient.out_eq' q.out.out).symm))
    _ = _ := D.transferNormNaturalityTransferNormOrbitEquiv_mk
      E L hL σ (Quotient.out q.out.out)

end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
