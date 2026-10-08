/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalizationClassGroup

set_option autoImplicit false
open scoped Classical IsMulCommutative NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory
open ClassFormation GlobalClassFields KummerTheory LocalClassFieldTheory Reciprocity
attribute [local instance] smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
  smallHilbertPrincipalization_ideleClassSubgroupNormal
variable (K : Type) [Field K] [NumberField K]

/-- Every ideal of a number field becomes principal after extension
to the selected small Hilbert class field. -/
theorem allIdealsBecomePrincipalInSmallHilbertClassField :
    ∀ I : Ideal (𝓞 K),
      (I.map
        (algebraMap
          (𝓞 K)
          (𝓞 (smallHilbertClassField K)))).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_ideal_map_isPrincipal
    (𝓞 K) (𝓞 (smallHilbertClassField K))).1
    (smallHilbertClassFieldClassGroupExtension_eq_one K)

/-- Every nonzero fractional ideal of a number field becomes a
principal fractional ideal after extension to the selected small
Hilbert class field. -/
theorem allFractionalIdealsBecomePrincipalInSmallHilbertClassField :
    ∀ I : FractionalIdealGroup K,
      FractionalIdealGroup.extension
          K (smallHilbertClassField K) I ∈
        (toPrincipalIdeal
          (𝓞 (smallHilbertClassField K))
          (smallHilbertClassField K)).range := by
  intro I
  apply
    (IdeleGroup.classGroup_mk_eq_one_iff
      (FractionalIdealGroup.extension
        K (smallHilbertClassField K) I)).1
  rw [
    FractionalIdealGroup.classGroup_mk_extension,
    smallHilbertClassFieldClassGroupExtension_eq_one]
  rfl

end IdealClassFieldTheory
end GlobalClassFieldTheory
