/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidue
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality


set_option autoImplicit false


open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u

/-- The commutative group structure on the quotient of ideles by principal ideles. -/
@[instance_reducible]
noncomputable def naturalityIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] naturalityIdeleClassCommGroup

local instance ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative


/-- Two finite Galois subextensions with the same underlying closed subgroup
are equal; the remaining structure fields are proof-irrelevant. -/
private theorem finiteGaloisSubextension_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    (A B : FiniteGaloisSubextension K)
    (h : A.field = B.field) :
    A = B := by
  cases A with
  | mk A hA nA fA =>
      cases B with
      | mk B hB nB fB =>
          dsimp only at h
          cases h
          rfl

/-- Rebase a finite Galois subextension along equality of its bundled base.
The field equality is the only data component; the remaining fields are
proof-irrelevant. -/
theorem finiteGaloisSubextension_transport_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    (Q : FiniteGaloisSubextension B.field)
    (hfield : P.field = Q.field) :
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField G =>
          FiniteGaloisSubextension X.field)
        hAB)
      P = Q := by
  cases hAB
  exact finiteGaloisSubextension_eq_of_field_eq P Q hfield

/-- Transporting an additive equivalence between rational ambient fixed
subgroups does not change the underlying direct-limit class. -/
theorem rationalAmbientFixedAddEquiv_transport_apply_val
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    {X : Type} [AddGroup X]
    (e : X ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (x : X) :
    ((Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            X ≃+ ambientFixedAddSubgroup
              rationalIdeleClassRepresentation Y.field)
          hAB)
        e x).1) =
      (e x).1 := by
  cases hAB
  rfl

/-- Changing only the bundled subgroup of an additive subgroup element
does not change its value in the ambient group. -/
private theorem addSubgroupCongr_apply_val
    {A : Type} [AddGroup A]
    {H K : AddSubgroup A}
    (h : H = K) (x : H) :
    ((AddEquiv.addSubgroupCongr h x).1 : A) = x.1 := by
  cases h
  rfl

/-- Transporting an idele class along a field equality and the corresponding
algebra equivalence leaves its rational direct-limit representative fixed. -/
theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]

/-- Transporting the target intermediate field of a base-field equivalence
preserves its rational fixed-part representative. -/
theorem rationalIdeleClassEquivFixed_transport_baseEquiv_val
    {T : Type} [Field T] [NumberField T]
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B) (e : T ≃ₐ[ℚ] B)
    (c : IdeleClassGroup T) :
    ((rationalIdeleClassEquivFixed A)
      (Additive.ofMul
        (ideleClassCongr (K := T) (M := A)
          (e.trans (IntermediateField.equivOfEq h).symm) c))).1 =
    ((rationalIdeleClassEquivFixed B)
      (Additive.ofMul (ideleClassCongr (K := T) (M := B) e c))).1 := by
  cases h
  have he :
      e.trans (IntermediateField.equivOfEq (rfl : A = A)).symm = e := by
    ext x
    rfl
  rw [he]

/-- Equality of the lower and upper closed subgroups transports the raw
extension quotient without exposing dependent rewrites to clients. -/
def extensionQuotientMulEquivOfEq
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal] :
    (H.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H J hJH) ≃*
      (H'.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H' J' hJH') := by
  cases hH
  cases hJ
  exact MulEquiv.refl _

/-- The quotient transport sends a quotient representative to the same
ambient group element, rebundled in the equal lower subgroup. -/
@[simp]
theorem extensionQuotientMulEquivOfEq_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal]
    (σ : H.toSubgroup) :
    extensionQuotientMulEquivOfEq hH hJ hJH hJH'
        (QuotientGroup.mk σ) =
      QuotientGroup.mk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup hH)) σ) := by
  cases hH
  cases hJ
  rfl

/-- Rebundling an element along equality of closed subgroups preserves its
underlying ambient group element. -/
theorem closedSubgroupCongr_apply_val
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' : ClosedSubgroup G}
    (hH : H = H') (σ : H.toSubgroup) :
    (((MulEquiv.subgroupCongr
        (congrArg ClosedSubgroup.toSubgroup hH)) σ).1 : G) = σ.1 := by
  cases hH
  rfl

/-- Rebase an abelianized extension-quotient equivalence together with its
finite abstract base. -/
def abelianizedExtensionQuotientAddEquiv_transportBase
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive
        (Abelianization
          (Eq.mp
            (congrArg
              (fun Y : FiniteAbstractField G =>
                FiniteGaloisSubextension Y.field)
              hAB)
            P).extensionQuotient) ≃+ X := by
  cases hAB
  exact e

/-- Rebase an abelianized equivalence along equality of finite Galois
subextensions over a fixed abstract base. -/
def abelianizedExtensionQuotientAddEquiv_transportExtension
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    {P Q : FiniteGaloisSubextension K}
    (hPQ : P = Q)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive (Abelianization Q.extensionQuotient) ≃+ X := by
  cases hPQ
  exact e

/-- The explicit quotient equivalence induced by rebasing a finite Galois
subextension. -/
def extensionQuotientMulEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q) :
    Q.extensionQuotient ≃* P.extensionQuotient := by
  cases hAB
  cases hPQ
  exact MulEquiv.refl _

/-- Quotient rebasing sends a canonical representative to the same ambient
group element rebundled in the old base subgroup. -/
@[simp]
theorem extensionQuotientMulEquiv_transportFiniteGalois_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    (σ : B.field.toSubgroup) :
    extensionQuotientMulEquiv_transportFiniteGalois hAB P hPQ
        (Q.extensionQuotientMk σ) =
      P.extensionQuotientMk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup
            (congrArg FiniteAbstractField.field hAB).symm)) σ) := by
  cases hAB
  cases hPQ
  rfl

/-- Abelianization commutes with simultaneous transport of the abstract base
and its finite Galois subextension. -/
theorem abelianizedCanonicalEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    {X : Type} [CommGroup X]
    (e : P.extensionQuotient ≃* X) :
    abelianizedExtensionQuotientAddEquiv_transportExtension hPQ
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P
          (MulEquiv.toAdditive
            (e.abelianizationCongr.trans
              (Abelianization.equivOfComm : X ≃* Abelianization X).symm))) =
      MulEquiv.toAdditive
        (((extensionQuotientMulEquiv_transportFiniteGalois
            hAB P hPQ).trans e).abelianizationCongr.trans
          (Abelianization.equivOfComm : X ≃* Abelianization X).symm) := by
  cases hAB
  cases hPQ
  rfl


/-- The finite norm-residue value, transported from the rational idele-class
representation and the abelianized extension quotient to the groups `C` and `X`. -/
def rationalFiniteNormResidueValue
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) : X := by
  letI :
      Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field L.field L.below) :=
    L.finite
  exact
    eGalois
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L
        (finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below (eIdele c)))

/-- The packaged norm-residue value is invariant under rebasing the finite
abstract field together with all dependent data. -/
theorem rationalFiniteNormResidueValue_transportBase
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A P eIdele eGalois c =
      rationalFiniteNormResidueValue B
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAB)
          P)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAB)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P eGalois)
        c := by
  cases hAB
  rfl

/-- The packaged norm-residue value is invariant under equality of the finite
Galois subextension. -/
theorem rationalFiniteNormResidueValue_transportExtension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    {P Q : FiniteGaloisSubextension K.field}
    (hPQ : P = Q)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue K P eIdele eGalois c =
      rationalFiniteNormResidueValue K Q eIdele
        (abelianizedExtensionQuotientAddEquiv_transportExtension
          hPQ eGalois)
        c := by
  cases hPQ
  rfl

/-- Evaluation of the canonical abelianization comparison induced by a
multiplicative equivalence into a commutative group. -/
theorem abelianizationCongrToComm_apply
    {Q R : Type*} [Group Q] [CommGroup R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        (e.abelianizationCongr.trans
          (Abelianization.equivOfComm : R ≃* Abelianization R).symm)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm
        (e.abelianizationCongr (Abelianization.of q)) = e q
  rw [abelianizationCongr_of]
  exact
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm_apply_apply _

/-- Evaluation of the canonical quotient from the abelianization of a
commutative group. -/
theorem commutativeAbelianizationEquiv_apply
    {Q R : Type*} [CommGroup Q] [Group R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm.trans e)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    e ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm
      (Abelianization.of q)) = e q
  exact congrArg e
    ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm_apply_apply q)


end Reciprocity
end GlobalClassFieldTheory
