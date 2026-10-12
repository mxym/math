/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocityBase

set_option autoImplicit false
open scoped Classical NumberField
noncomputable section
namespace GlobalClassFieldTheory
namespace GlobalClassFields
open NumberField
open Reciprocity
attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative
private theorem mulEquiv_toEquiv_apply
    {A B : Type*} [Mul A] [Mul B]
    (e : A ≃* B) (x : A) : e.toEquiv x = e x := by rfl

private theorem continuousMulEquiv_toMulEquiv_apply
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Mul A] [Mul B]
    (e : A ≃ₜ* B) (x : A) : e.toMulEquiv x = e x := by rfl

variable {K : Type} [Field K] [NumberField K]


/-- Evaluation of ray class reciprocity is global reciprocity transported
through the equality of the ray norm subgroup and the idele norm range. -/
theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
    (m : RayClass.Modulus K)
    (σ : Gal((rayClassField K m) / K)) :
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m σ =
      QuotientGroup.quotientMulEquivOfEq
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m)
        (arithmeticGlobalReciprocityContinuousMulEquiv
          K (rayClassField K m) σ) := by
  simp only [arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup,
    ContinuousMulEquiv.trans, MulEquiv.trans, Equiv.trans,
    ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    Function.comp_apply,
    mulEquiv_toEquiv_apply]
  have h := continuousMulEquiv_toMulEquiv_apply
    (arithmeticGlobalReciprocityContinuousMulEquiv K (rayClassField K m)) σ
  with_reducible exact congrArg (fun q => QuotientGroup.quotientMulEquivOfEq (rayClassField_ideleClassNorm_range_over_original (K := K) m) q) h

end GlobalClassFields
end GlobalClassFieldTheory
