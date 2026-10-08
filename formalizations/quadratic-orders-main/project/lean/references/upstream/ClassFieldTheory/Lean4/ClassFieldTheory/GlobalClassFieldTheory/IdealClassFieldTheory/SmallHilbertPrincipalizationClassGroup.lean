/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalizationIdele

set_option autoImplicit false
open scoped Classical IsMulCommutative NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory
open ClassFormation GlobalClassFields KummerTheory LocalClassFieldTheory Reciprocity
attribute [local instance] smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
  smallHilbertPrincipalization_ideleClassSubgroupNormal
variable (K : Type) [Field K] [NumberField K]

private theorem smallHilbertClassFieldClassGroupExtension_apply_eq_one
    (c : ClassGroup (𝓞 K)) :
    ClassGroup.extendedHom
        (𝓞 K) (𝓞 (smallHilbertClassField K)) c =
      (1 : ClassGroup (𝓞 (smallHilbertClassField K))) := by
  obtain ⟨q, rfl⟩ :=
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).surjective c
  have hidele :=
    smallHilbertClassFieldIdeleExtensionMap_apply_eq_one K q
  have hnaturality :=
    smallHilbertClassFieldIdeleExtensionMap_naturality
      K (smallHilbertClassField K) q
  calc
    ClassGroup.extendedHom
          (𝓞 K) (𝓞 (smallHilbertClassField K))
          (smallHilbertClassFieldQuotientEquivClassGroup (K := K) q) =
        smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K)
          (smallHilbertClassFieldIdeleExtensionMap
            K (smallHilbertClassField K) q) :=
      hnaturality.symm
    _ = smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K) 1 :=
      congrArg
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassField K)) hidele
    _ = 1 :=
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := smallHilbertClassField K)).map_one

/-- Extension of ideal classes from a number field to its selected
small Hilbert class field is the trivial homomorphism.  This follows
directly from the naturality equality identifying actual idele
extension with actual extension of ideal classes. -/
theorem smallHilbertClassFieldClassGroupExtension_eq_one :
    @Eq
      (ClassGroup (𝓞 K) →*
        ClassGroup (𝓞 (smallHilbertClassField K)))
      (ClassGroup.extendedHom
        (𝓞 K) (𝓞 (smallHilbertClassField K)))
      (1 : ClassGroup (𝓞 K) →*
        ClassGroup (𝓞 (smallHilbertClassField K))) := by
  apply MonoidHom.ext
  intro c
  simpa only [MonoidHom.one_apply] using
    smallHilbertClassFieldClassGroupExtension_apply_eq_one K c

end IdealClassFieldTheory
end GlobalClassFieldTheory
