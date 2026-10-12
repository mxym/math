/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActualEquiv

set_option autoImplicit false
open scoped Classical IsMulCommutative NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace GlobalClassFields
open Reciprocity
variable {K : Type} [Field K] [NumberField K]
attribute [local instance] bigHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

/-- Representative form of big-Hilbert reciprocity: the global
norm-residue symbol of an actual idèle maps to its narrow ideal
class, with only the canonical base-field transport remaining. -/
@[simp]
theorem bigHilbertClassFieldGaloisEquivNarrowClassGroup_idele
    (a : IdeleGroup (bigHilbertClassFieldBase K)) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroup (K := K)
        (globalNormResidueMonoidHom
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup
              (bigHilbertClassFieldBase K)) a)) =
      bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm
        (QuotientGroup.mk'
          (RayClass.narrowDenominator
            (K := bigHilbertClassFieldBase K)) a) := by
  calc
    _ = bigHilbertNarrowClassGroupCongr
          (bigHilbertClassFieldBaseEquiv (K := K)).symm
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := bigHilbertClassFieldBase K)
            (QuotientGroup.mk'
              (bigHilbertClassFieldNormSubgroup
                (K := bigHilbertClassFieldBase K))
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup
                  (bigHilbertClassFieldBase K)) a))) :=
      (bigHilbertClassFieldReciprocityData (K := K)).2 _
    _ = _ :=
      congrArg
        (bigHilbertNarrowClassGroupCongr
          (bigHilbertClassFieldBaseEquiv (K := K)).symm)
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
          (K := bigHilbertClassFieldBase K) a)

end GlobalClassFields
end GlobalClassFieldTheory
