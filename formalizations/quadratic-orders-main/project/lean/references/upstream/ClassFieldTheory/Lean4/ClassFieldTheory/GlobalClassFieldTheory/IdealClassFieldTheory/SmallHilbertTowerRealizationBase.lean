/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation
import Mathlib.Data.Rat.Cast.Defs


set_option autoImplicit false

/-!
# Actual realization of the two-stage small Hilbert tower

The first small Hilbert class field is the actual finite abelian
subextension selected in `HilbertClassFieldRealization`.  Over its actual
fixed field, the closed finite-index small-Hilbert norm subgroup has a
finite Galois norm neighbourhood.  We embed that neighbourhood in the
rational separable closure compatibly with the already chosen first
stage.  Finite abelian classification then selects the second small
Hilbert class field over the literal first-stage subgroup.

The compatibility of the embedding is essential: an unrelated chosen
copy of the middle number field would produce a class field over a
conjugate closed subgroup rather than over the first-stage subgroup
itself.
-/

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

/-- The ordinary idèle-class operations used by the two-stage transport,
fixed at the canonical principal-subgroup quotient. -/
@[instance_reducible]
noncomputable def smallHilbertTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertTowerIdeleClassCommGroup

private theorem addSubgroup_comap_symm_eq_map
    {A B : Type*} [AddGroup A] [AddGroup B]
    (H : AddSubgroup A) (e : A ≃+ B) :
    H.comap e.symm.toAddMonoidHom =
      H.map e.toAddMonoidHom := by
  exact (AddSubgroup.map_equiv_eq_comap_symm e H).symm

private noncomputable abbrev
    closedFiniteIndexNormAmbientCanonicalBaseAlgebra
    (F : Type) [Field F] [NumberField F]
    (H : Subgroup (IdeleClassGroup F))
    (hclosed : IsClosed (H : Set (IdeleClassGroup F)))
    [H.FiniteIndex] :
    Algebra F
      (closedFiniteIndexClassFieldNormAmbient
        (K := F) H hclosed) :=
  inferInstance

section RationalFixedField

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)

/-- The finite abstract field attached to the intermediate field of the
finite abelian extension, with finiteness obtained by transitivity. -/
noncomputable abbrev smallHilbertTowerMiddleFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  { field := L.field
    finite := by
      let : Finite
          ((baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
            extensionSubgroup
              (baseField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
              K.field (le_baseField K.field)) :=
        K.finite
      let : Finite
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) :=
        L.finite
      exact
        FiniteGaloisSubextension.finite_extension_trans
          L.below (le_baseField K.field) }

local notation "E" =>
  abstractFixedField ℚ (SeparableClosure ℚ) L.field

local notation "N" =>
  smallHilbertClassFieldNormAmbient E

noncomputable instance
    smallHilbertTowerMiddleAbstractQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          L.field (le_baseField L.field)) :=
  (smallHilbertTowerMiddleFiniteAbstractField K L).finite

private noncomputable instance
    smallHilbertTowerMiddleFiniteDimensional :
    FiniteDimensional ℚ E :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) L.field inferInstance

private noncomputable instance
    smallHilbertTowerMiddleNumberField :
    NumberField E :=
  NumberField.of_module_finite ℚ E


/-- The small Hilbert norm subgroup of the intermediate number field,
transported to its ambient fixed idele-class representation. -/
noncomputable def smallHilbertTowerMiddleNormSubgroup :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field) :=
  (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup.comap
    (rationalAbstractFixedFieldIdeleClassEquivFixed
      L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).symm.toAddMonoidHom

/-- The typed `comap` endpoint is the canonical transported `map` endpoint.
This uses only the generic additive equivalence law. -/
theorem smallHilbertTowerMiddleNormSubgroup_eq_map :
    smallHilbertTowerMiddleNormSubgroup K L =
      (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup.map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field
          (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L)).toAddMonoidHom := by
  exact addSubgroup_comap_symm_eq_map
    (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup
    (rationalAbstractFixedFieldIdeleClassEquivFixed L.field
      (hfinite := smallHilbertTowerMiddleAbstractQuotientFinite K L))

/-- The algebra structure of the intermediate field on its small Hilbert
class-field norm ambient. -/
@[reducible]
noncomputable def
    smallHilbertTowerNormAmbientAlgebra :
    Algebra E N :=
  closedFiniteIndexNormAmbientCanonicalBaseAlgebra E
    (smallHilbertClassFieldNormSubgroup (K := E))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := E))

attribute [local instance] smallHilbertTowerNormAmbientAlgebra

/-- Scalar multiplication of the intermediate field on its small Hilbert
class-field norm ambient. -/
@[reducible]
noncomputable def
    smallHilbertTowerNormAmbientSMul :
    SMul E N :=
  Algebra.toSMul
    (self := smallHilbertTowerNormAmbientAlgebra K L)

@[reducible]
private noncomputable def
    smallHilbertTowerNormAmbientModule :
    Module E N :=
  @Algebra.toModule E N _ _
    (smallHilbertTowerNormAmbientAlgebra K L)

theorem
    smallHilbertTowerNormAmbientScalarTower :
    @IsScalarTower ℚ E N
      (Algebra.toSMul (R := ℚ) (A := E))
      (smallHilbertTowerNormAmbientSMul K L)
      (Algebra.toSMul (R := ℚ) (A := N)) := by
  exact IsScalarTower.of_algebraMap_eq'
    (R := ℚ) (S := E) (A := N)
    (RingHom.ext_rat (algebraMap ℚ N)
      ((algebraMap E N).comp (algebraMap ℚ E)))

/-- The rational algebra embedding of the intermediate field into its
small Hilbert class-field norm ambient. -/
noncomputable def
    smallHilbertTowerNormAmbientAlgHom :
    E →ₐ[ℚ] N :=
  { toRingHom := algebraMap E N
    commutes' := fun r =>
      (RingHom.congr_fun
        (RingHom.ext_rat
          ((algebraMap E N).comp (algebraMap ℚ E))
          (algebraMap ℚ N)) r) }

theorem smallHilbertTowerNormAmbientAlgHom_apply
    (x : E) :
    smallHilbertTowerNormAmbientAlgHom K L x =
      algebraMap E N x := by
  rfl

theorem
    smallHilbertTowerNormAmbientIsGalois :
    IsGalois E N := by
  unfold smallHilbertClassFieldNormAmbient
    closedFiniteIndexClassFieldNormAmbient
  exact
    closedFiniteIndexNormAmbientIsGalois
      (smallHilbertClassFieldNormSubgroup (K := E))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := E))

attribute [local instance] smallHilbertTowerNormAmbientIsGalois

/-- The separable-closure automorphism extending the induced embedding
of the intermediate field into the norm-neighborhood field. -/
noncomputable def
    smallHilbertNormNeighborhoodForwardAlignment :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ := by
  let j₀ : N →ₐ[ℚ] SeparableClosure ℚ :=
    numberFieldSeparableClosureEmbedding N
  let i₀ : E →ₐ[ℚ] SeparableClosure ℚ :=
    j₀.comp (smallHilbertTowerNormAmbientAlgHom K L)
  exact
    AlgEquiv.ofBijective
      (i₀.liftNormal (SeparableClosure ℚ))
      (AlgHom.normal_bijective
        ℚ (SeparableClosure ℚ) (SeparableClosure ℚ) _)

/-- The separable-closure automorphism which aligns an arbitrary chosen
embedding of the norm-neighbourhood field with the already embedded
middle field. -/
noncomputable def
    smallHilbertNormNeighborhoodAlignment :
    SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
  (smallHilbertNormNeighborhoodForwardAlignment K L).symm

@[simp]
theorem smallHilbertNormNeighborhoodForwardAlignment_apply
    (x : E) :
    smallHilbertNormNeighborhoodForwardAlignment K L
        (x : SeparableClosure ℚ) =
      (numberFieldSeparableClosureEmbedding N)
        (algebraMap E N x) := by
  let j₀ : N →ₐ[ℚ] SeparableClosure ℚ :=
    numberFieldSeparableClosureEmbedding N
  let i₀ : E →ₐ[ℚ] SeparableClosure ℚ :=
    j₀.comp (smallHilbertTowerNormAmbientAlgHom K L)
  dsimp only [smallHilbertNormNeighborhoodForwardAlignment,
    AlgEquiv.ofBijective_apply]
  calc
    _ = i₀ x := by
      simpa only [IntermediateField.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] using
        i₀.liftNormal_commutes (SeparableClosure ℚ) x
    _ = j₀ (algebraMap E N x) := by
      change
        j₀ (smallHilbertTowerNormAmbientAlgHom K L x) =
          j₀ (algebraMap E N x)
      exact congrArg j₀
        (smallHilbertTowerNormAmbientAlgHom_apply K L x)


end RationalFixedField
end IdealClassFieldTheory
end GlobalClassFieldTheory
