/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocityNormResidue

set_option autoImplicit false
open scoped Classical NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace GlobalClassFields
open NumberField
open Reciprocity
attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative
variable {K : Type} [Field K] [NumberField K]

/-- Inverse arithmetic ray reciprocity sends a represented ray class
back to the arithmetic global norm-residue symbol. -/
@[simp]
theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_symm_mk
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    (arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
      (K := K) m).symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      arithmeticGlobalNormResidueMonoidHom
        K (rayClassField K m) c := by
  let e :=
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
      (K := K) m
  apply e.injective
  calc
    e (e.symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c)) =
        QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c :=
      e.apply_symm_apply _
    _ = e
          (arithmeticGlobalNormResidueMonoidHom
            K (rayClassField K m) c) :=
      (arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
        (K := K) m c).symm

end GlobalClassFields
end GlobalClassFieldTheory
