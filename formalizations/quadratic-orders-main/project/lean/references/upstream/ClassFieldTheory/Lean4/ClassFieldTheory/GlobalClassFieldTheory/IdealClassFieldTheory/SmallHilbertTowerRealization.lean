/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealizationSecond

set_option autoImplicit false

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open AlgebraicNumberTheory
open ClassFormation
open CyclicCohomology
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open RamificationTheory
open Reciprocity


attribute [local instance] smallHilbertTowerIdeleClassCommGroup
  smallHilbertTowerNormAmbientAlgebra
  smallHilbertTowerNormAmbientIsGalois

section RationalFixedField

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)


local notation "E" => abstractFixedField ℚ (SeparableClosure ℚ) L.field
local notation "N" => smallHilbertClassFieldNormAmbient E

end RationalFixedField

section ActualTower

variable (K : Type) [Field K] [NumberField K]

/-- The actual second small Hilbert class field over the selected first
small Hilbert class field of `K`. -/
noncomputable def smallHilbertTowerSecondSubextension :
    FiniteAbelianSubextension
      (smallHilbertClassFieldSubextension K).field :=
  secondSmallHilbertClassFieldSubextension
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- Exact norm-subgroup equation for the actual second stage. -/
@[simp]
theorem smallHilbertTowerSecondSubextension_normSubgroup :
    (smallHilbertTowerSecondSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertTowerMiddleNormSubgroup
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K))
        (smallHilbertClassFieldSubextension K) :=
  secondSmallHilbertClassFieldSubextension_normSubgroup
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- The actual two-stage small Hilbert tower, packaged as a finite
Galois subextension of the original selected base subgroup. -/
noncomputable def smallHilbertTowerGaloisRealization :
    FiniteGaloisSubextension
      (smallHilbertClassFieldBaseSubgroup K) :=
  smallHilbertClassFieldGaloisSubextension
    (numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)
    (smallHilbertTowerSecondSubextension K)
    ((smallHilbertTowerSecondSubextension_normSubgroup K).trans
      (smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K))
        (smallHilbertClassFieldSubextension K)))

end ActualTower

end IdealClassFieldTheory
end GlobalClassFieldTheory
