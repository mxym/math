/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActualData

set_option autoImplicit false
open scoped Classical IsMulCommutative NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace GlobalClassFields
open Reciprocity
variable {K : Type} [Field K] [NumberField K]
attribute [local instance] bigHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

/-- The reciprocity equivalence from the actual big Hilbert Galois group
to the narrow class group of the original number field. -/
noncomputable def bigHilbertClassFieldGaloisEquivNarrowClassGroup :
    Gal((bigHilbertClassField K) /
        (bigHilbertClassFieldBase K)) ≃*
      RayClass.NarrowClassGroup K :=
  (bigHilbertClassFieldReciprocityData (K := K)).1

/-- Under big-Hilbert reciprocity, the actual global norm-residue
symbol is the narrow ideal class of its idèle-class representative,
transported back to the original number field. -/
@[simp]
theorem bigHilbertClassFieldGaloisEquivNarrowClassGroup_globalNormResidue
    (c : IdeleClassGroup (bigHilbertClassFieldBase K)) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroup (K := K)
        (globalNormResidueMonoidHom
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K) c) =
      bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := bigHilbertClassFieldBase K)
          (QuotientGroup.mk'
            (bigHilbertClassFieldNormSubgroup
              (K := bigHilbertClassFieldBase K)) c)) := by
  exact (bigHilbertClassFieldReciprocityData (K := K)).2 c


end GlobalClassFields
end GlobalClassFieldTheory
