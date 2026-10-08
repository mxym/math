/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertPrincipalizationBase

set_option autoImplicit false
open scoped Classical IsMulCommutative NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory
open ClassFormation GlobalClassFields KummerTheory LocalClassFieldTheory Reciprocity
attribute [local instance] smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
  smallHilbertPrincipalization_ideleClassSubgroupNormal
variable (K : Type) [Field K] [NumberField K]

/-- The map induced by genuine idele extension from the original
number field on the two small-Hilbert reciprocity quotients is
trivial. -/
theorem smallHilbertClassFieldIdeleExtensionMap_eq_one :
    @Eq
      ((IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) →*
        (IdeleClassGroup (smallHilbertClassField K) ⧸
          smallHilbertClassFieldNormSubgroup
            (K := smallHilbertClassField K)))
      (smallHilbertClassFieldIdeleExtensionMap
        K (smallHilbertClassField K))
      (1 :
        (IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) →*
        (IdeleClassGroup (smallHilbertClassField K) ⧸
          smallHilbertClassFieldNormSubgroup
            (K := smallHilbertClassField K))) := by
  apply MonoidHom.ext
  intro q
  simpa only [MonoidHom.one_apply] using
    smallHilbertClassFieldIdeleExtensionMap_apply_eq_one K q

end IdealClassFieldTheory
end GlobalClassFieldTheory
