/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusRestriction


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

/-- The transfer-orbit index set
`⟨σ⟩ \ G(\widetilde L/K) / H` is canonically the norm double-coset
index set `G_K' \ G_K / G_Σ`.  The equivalence is inversion of double
cosets, followed by passage from powers of `σ` to their closure `Γ` and
the canonical identification `G_K/G_Σ ≃ G(\widetilde L/K)/Γ`. -/
noncomputable def transferNormNaturalityTransferNormOrbitEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)) ≃
      Quotient (orbitRel
        (extensionSubgroup E.base.field E.field.field E.below)
        (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ))) := by
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let M := extensionSubgroup E.base.field E.field.field E.below
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let f : M →* H := D.transferNormNaturalityIntermediateToFrobeniusSubgroup
    E L hL
  let e := D.frobeniusFixedCosetClosureEquiv
    E.base L (hL.trans E.below) σ
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  have hΓ :
      (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup = Γ.toSubgroup := by
    simp only [Γ, DegreeData.frobeniusClosure, Set.range_const]
  let eΓ : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup ≃
      P ⧸ Γ.toSubgroup := Subgroup.quotientEquivOfEq hΓ
  have heΓ (h : H)
      (x : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup) :
      eΓ (h • x) = h • eΓ x := by
    refine Quotient.inductionOn' x ?_
    intro p
    change eΓ (QuotientGroup.mk (h.val * p)) = h • eΓ (QuotientGroup.mk p)
    simp only [eΓ, Subgroup.quotientEquivOfEq_mk]
    rfl
  let eΓorbit := orbitQuotientEquivOfSurjectiveEquivariant
    (MonoidHom.id H) Function.surjective_id eΓ heΓ
  have hf : Function.Surjective f :=
    D.transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
      E L hL
  have he (m : M)
      (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK) :
      e (m • x) = f m • e x := by
    exact D.frobeniusFixedCosetClosureEquiv_equivariant
      E L hL σ m x
  let eAction := orbitQuotientEquivOfSurjectiveEquivariant f hf e he
  exact (orbitQuotientSwapEquiv (Subgroup.zpowers σ.1) H).trans
    ((orbitQuotientClosedCyclicEquiv H hHclosed σ.1).trans
      (eΓorbit.trans eAction.symm))


end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
