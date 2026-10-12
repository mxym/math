/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTheorem
import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTransfer
import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified


set_option autoImplicit false

/-!
# Principalization in the selected small Hilbert class field

The selected second small Hilbert class field is Galois over the
canonical fixed-field copy of the original base, and its maximal
abelian intermediate field is the selected first small Hilbert class
field.  Witt transfer therefore places every idele class extended from
that fixed-field copy in the norm range from the second stage.
Functoriality of actual idele extension along the degree-one
identification of the original field with its fixed-field copy gives
the same range inclusion for idele classes extended from the original
field itself.

The exact second-stage norm subgroup is the intrinsic small-Hilbert
subgroup, so the genuine map from the original field on small-Hilbert
quotients is trivial.  Its naturality with extension of ideal classes
then gives the class-group, integral-ideal, and fractional-ideal forms
of principalization over the original number field.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

local instance
    smallHilbertPrincipalization_ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    smallHilbertPrincipalization_ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

/-- A generic field-extension form keeps the class-field construction opaque. -/
theorem smallHilbertExtension_trivial_of_range
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (h : (ideleClassExtension K L).range ≤
      smallHilbertClassFieldNormSubgroup (K := L))
    (q : IdeleClassGroup K ⧸ smallHilbertClassFieldNormSubgroup (K := K)) :
    smallHilbertClassFieldIdeleExtensionMap K L q = 1 := by
  refine QuotientGroup.induction_on q ?_
  intro c
  exact (smallHilbertClassFieldIdeleExtensionMap_mk' K L c).trans
    ((QuotientGroup.eq_one_iff (ideleClassExtension K L c)).mpr (h ⟨c, rfl⟩))

variable (K : Type) [Field K] [NumberField K]

/-- Extension to the small Hilbert class field sends each reciprocity
quotient class to the identity class. -/
theorem smallHilbertClassFieldIdeleExtensionMap_apply_eq_one
    (q : IdeleClassGroup K ⧸
      smallHilbertClassFieldNormSubgroup (K := K)) :
    smallHilbertClassFieldIdeleExtensionMap
        K (smallHilbertClassField K) q =
      (1 : IdeleClassGroup (smallHilbertClassField K) ⧸
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K)) := by
  have hcontainment :=
    smallHilbertClassField_ideleClassExtension_range_le_secondNormRange K
  unfold smallHilbertClassFieldSecondNormRangeContainment at hcontainment
  exact smallHilbertExtension_trivial_of_range K (smallHilbertClassField K)
    hcontainment q

end IdealClassFieldTheory
end GlobalClassFieldTheory
