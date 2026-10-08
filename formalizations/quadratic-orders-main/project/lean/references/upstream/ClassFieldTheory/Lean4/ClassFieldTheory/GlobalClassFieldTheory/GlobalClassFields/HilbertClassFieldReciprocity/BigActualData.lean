/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldNaturality
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison


set_option autoImplicit false

/-!
# Big Hilbert reciprocity over the realized base field

This leaf specializes the shared reciprocity transport to the actual base
field of the selected big Hilbert class field.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

local instance
    bigHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

/-- The actual norm range of the selected big Hilbert class field is
the intrinsic big-Hilbert norm subgroup of its actual base field. -/
theorem bigHilbertClassField_ideleClassNorm_range_eq_intrinsic :
    (_root_.ideleClassNorm
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).range =
      bigHilbertClassFieldNormSubgroup
        (K := bigHilbertClassFieldBase K) := by
  rw [bigHilbertClassField_ideleClassNorm_range]
  exact
    bigHilbertClassFieldNormSubgroup_map_ideleClassCongr
      (bigHilbertClassFieldBaseEquiv (K := K))

/-- Global reciprocity identifies the genuine Galois group of the
selected big Hilbert class field with the narrow ideal class group of
the original number field. -/
noncomputable def bigHilbertClassFieldReciprocityData :
    {e : Gal((bigHilbertClassField K) /
          (bigHilbertClassFieldBase K)) ≃*
        RayClass.NarrowClassGroup K //
      ∀ c : IdeleClassGroup (bigHilbertClassFieldBase K),
        e (globalNormResidueMonoidHom
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K) c) =
          bigHilbertNarrowClassGroupCongr
            (bigHilbertClassFieldBaseEquiv (K := K)).symm
            (bigHilbertClassFieldQuotientEquivNarrowClassGroup
              (K := bigHilbertClassFieldBase K)
              (QuotientGroup.mk'
                (bigHilbertClassFieldNormSubgroup
                  (K := bigHilbertClassFieldBase K)) c))} := by
  let d := hilbertClassFieldGlobalReciprocityTransportData
    (bigHilbertClassFieldNormSubgroup
      (K := bigHilbertClassFieldBase K))
    (bigHilbertClassField_ideleClassNorm_range_eq_intrinsic
      (K := K))
    ((bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := bigHilbertClassFieldBase K)).trans
      (bigHilbertNarrowClassGroupCongr
        (bigHilbertClassFieldBaseEquiv (K := K)).symm))
  refine ⟨d.1, ?_⟩
  intro c
  exact d.2 c


end GlobalClassFields
end GlobalClassFieldTheory
