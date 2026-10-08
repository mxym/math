/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization


set_option autoImplicit false

/-!
# Arithmetic reciprocity for actual ray class fields

This is the canonical topological isomorphism
`Gal(Kᵐ/K) ≃ₜ* C_K/C_Kᵐ` with arithmetic Frobenius
normalization.  It uses the actual selected ray class field, its exact
idèle norm range, the finite Krull topology, and the native ray-class
quotient topology.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

theorem arithmeticRayClassIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

/-- Arithmetic reciprocity followed by transport between equal norm
quotients sends a norm-residue symbol to its represented quotient class. -/
theorem
    arithmeticReciprocity_quotientMulEquivOfEq_globalNormResidue
    {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (c : IdeleClassGroup F) :
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
      QuotientGroup.mk' H c := by
  let e := arithmeticGlobalReciprocityContinuousMulEquiv F E
  let q :=
    QuotientGroup.mk'
      (_root_.ideleClassNorm F E).range c
  have hsymm :
      e.symm q = arithmeticGlobalNormResidueMonoidHom F E c :=
    arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk F E c
  have he :
      e (arithmeticGlobalNormResidueMonoidHom F E c) = q := by
    calc
      e (arithmeticGlobalNormResidueMonoidHom F E c) =
          e (e.symm q) :=
        congrArg (fun σ => e σ) hsymm.symm
      _ = q := e.apply_symm_apply q
  calc
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
        QuotientGroup.quotientMulEquivOfEq h q :=
      congrArg (fun x => QuotientGroup.quotientMulEquivOfEq h x) he
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

/-- Arithmetic global reciprocity for the actual selected ray class
field, bundled with both native topologies. -/
noncomputable def
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃ₜ*
      RayClass.RayClassGroup m := by
  letI normQuotientDiscreteTopology : DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm
          K (rayClassField K m)).range) :=
    ideleClassNormQuotient_discreteTopology
      K (rayClassField K m)
  letI rayClassGroupDiscreteTopology : DiscreteTopology
      (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup m)
  let quotientTransport :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm
            K (rayClassField K m)).range) ≃ₜ*
        RayClass.RayClassGroup m :=
    { QuotientGroup.quotientMulEquivOfEq
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact
    (arithmeticGlobalReciprocityContinuousMulEquiv
      K (rayClassField K m)).trans
        quotientTransport

end GlobalClassFields
end GlobalClassFieldTheory
