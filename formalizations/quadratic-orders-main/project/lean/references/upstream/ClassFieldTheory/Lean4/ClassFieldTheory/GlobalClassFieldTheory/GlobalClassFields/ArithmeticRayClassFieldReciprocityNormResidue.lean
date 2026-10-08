/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocityEvaluation

set_option autoImplicit false
open scoped Classical NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace GlobalClassFields
open NumberField
open Reciprocity
attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative
variable {K : Type} [Field K] [NumberField K]

/-- Arithmetic ray-class reciprocity sends the arithmetic global
norm-residue symbol of an idèle class to its literal ray class. -/
@[simp]
theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (arithmeticGlobalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  calc
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (arithmeticGlobalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.quotientMulEquivOfEq
          (rayClassField_ideleClassNorm_range_over_original
            (K := K) m)
          (arithmeticGlobalReciprocityContinuousMulEquiv
            K (rayClassField K m)
            (arithmeticGlobalNormResidueMonoidHom
              K (rayClassField K m) c)) :=
      arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
        (K := K) m _
    _ = QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c :=
      arithmeticReciprocity_quotientMulEquivOfEq_globalNormResidue
        (RayClass.Modulus.congruenceSubgroup m)
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m) c

end GlobalClassFields
end GlobalClassFieldTheory
