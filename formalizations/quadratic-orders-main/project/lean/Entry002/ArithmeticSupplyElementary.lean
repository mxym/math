import Entry002.Orders
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.NumberField.Norm

/-! Elementary arithmetic supply bridges. These prove the norm-prime quotient
and conductor reduction steps without asserting ray class fields or density. -/

namespace Entry002

open Module

section PrincipalQuotient

variable {O : Type*} [CommRing O] [IsDomain O]
  [Module.Free ℤ O] [Module.Finite ℤ O]

/-- The index/norm identity for a principal ideal in a finite free integral
ring. In particular it applies to nonmaximal conductor orders, without a
Dedekind-domain assumption. -/
theorem arithmeticSupply_principal_quotient_card (a : O) (ha : a ≠ 0) :
    Nat.card (O ⧸ Ideal.span ({a} : Set O)) = (Algebra.norm ℤ a).natAbs := by
  let b := Module.Free.chooseBasis ℤ O
  let I := Ideal.span ({a} : Set O)
  let e := b.equiv (Ideal.basisSpanSingleton b ha) (Equiv.refl _)
  have h := Submodule.natAbs_det_equiv (I.restrictScalars ℤ) e
  change (LinearMap.det ((I.restrictScalars ℤ).subtype ∘ₗ
    AddMonoidHom.toIntLinearMap (e : O →+ I))).natAbs =
      Nat.card (O ⧸ I) at h
  rw [Algebra.norm_apply]
  calc
    Nat.card (O ⧸ I) =
        (LinearMap.det ((I.restrictScalars ℤ).subtype ∘ₗ
          AddMonoidHom.toIntLinearMap (e : O →+ I))).natAbs := h.symm
    _ = (LinearMap.det (Algebra.lmul ℤ O a)).natAbs := by
      congr 2
      apply b.ext
      intro i
      change (e (b i) : O) = a * b i
      dsimp [e]
      rw [b.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]

/-- A genuine norm-prime element gives a surjective unital residue ring map
whose kernel is precisely its principal ideal. No irreducibility assumption
on the element and no maximal-order assumption are required. -/
theorem arithmeticSupply_exists_normPrime_residueHom (p : ℕ) (hp : Nat.Prime p)
    (a : O) (hnorm : (Algebra.norm ℤ a).natAbs = p) :
    ∃ ψ : O →+* ZMod p, Function.Surjective ψ ∧ ∀ x : O, ψ x = 0 ↔ a ∣ x := by
  have ha : a ≠ 0 := by
    intro hzero
    rw [hzero, Algebra.norm_zero, Int.natAbs_zero] at hnorm
    exact hp.ne_zero hnorm.symm
  let I := Ideal.span ({a} : Set O)
  have hcard : Nat.card (O ⧸ I) = p :=
    (arithmeticSupply_principal_quotient_card a ha).trans hnorm
  have : Finite (O ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
  let := Fintype.ofFinite (O ⧸ I)
  have hcard' : Fintype.card (O ⧸ I) = p := by simpa only [Nat.card_eq_fintype_card] using hcard
  let e := (ZMod.ringEquivOfPrime (O ⧸ I) hp hcard').symm
  let ψ := e.toRingHom.comp (Ideal.Quotient.mk I)
  refine ⟨ψ, e.surjective.comp (Ideal.Quotient.mk_surjective), ?_⟩
  intro x
  change e (Ideal.Quotient.mk I x) = 0 ↔ a ∣ x
  rw [← e.map_zero, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

/-- Principal ideals of norm-prime generators are maximal in every finite
free integral order, including nonmaximal ones. -/
theorem arithmeticSupply_normPrime_isMaximal (p : ℕ) (hp : Nat.Prime p)
    (a : O) (hnorm : (Algebra.norm ℤ a).natAbs = p) :
    (Ideal.span ({a} : Set O)).IsMaximal := by
  obtain ⟨ψ, honto, hker⟩ := arithmeticSupply_exists_normPrime_residueHom p hp a hnorm
  have : Fact p.Prime := ⟨hp⟩
  have hI : RingHom.ker ψ = Ideal.span ({a} : Set O) := by
    ext x
    exact (hker x).trans Ideal.mem_span_singleton.symm
  rw [← hI]
  exact RingHom.ker_isMaximal_of_surjective ψ honto

/-- The paired-kernel intersection is elementary once the two norm-prime
principal ideals are genuinely distinct and their product is associated to
the rational prime. Neither prerequisite is replaced by a surrogate. -/
theorem arithmeticSupply_pair_intersection (p : ℕ) (hp : Nat.Prime p) (a b : O)
    (ha : (Algebra.norm ℤ a).natAbs = p) (hb : (Algebra.norm ℤ b).natAbs = p)
    (hne : Ideal.span ({a} : Set O) ≠ Ideal.span ({b} : Set O))
    (hprod : Associated (a * b) (p : O)) (x : O) :
    (a ∣ x ∧ b ∣ x) ↔ ∃ y : O, x = (p : ℤ) • y := by
  have : (Ideal.span ({a} : Set O)).IsMaximal := arithmeticSupply_normPrime_isMaximal p hp a ha
  have : (Ideal.span ({b} : Set O)).IsMaximal := arithmeticSupply_normPrime_isMaximal p hp b hb
  have hcop : IsCoprime a b := (Ideal.isCoprime_span_singleton_iff a b).mp
    (Ideal.isCoprime_of_isMaximal hne)
  have hpair : (a ∣ x ∧ b ∣ x) ↔ a * b ∣ x :=
    ⟨fun h => hcop.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩⟩
  rw [hpair, hprod.dvd_iff_dvd_left]
  simp only [dvd_def, zsmul_eq_mul, Int.cast_natCast]

end PrincipalQuotient

section ConductorReduction

variable (K : Type*) [Field K] [NumberField K] (f p : ℕ)

/-- An actual integral generator congruent to one modulo the conductor
has an actual representative in the nonmaximal conductor order. -/
theorem arithmeticSupply_congruenceOne_order_lift
    (a : NumberField.RingOfIntegers K)
    (hcong : (f : NumberField.RingOfIntegers K) ∣ a - 1) :
    ∃ x : conductorOrder K f, conductorOrderToIntegers K f x = a := by
  obtain ⟨y, hy⟩ := hcong
  have hco := congrArg (fun z : NumberField.RingOfIntegers K => (z : K)) hy
  change (a : K) - 1 = (f : K) * (y : K) at hco
  have hm : (a : K) ∈ conductorOrder K f := by
    refine ⟨1, y, ?_⟩
    simp only [Int.cast_one]
    calc
      _ = ((a : K) - 1) + 1 := by ring
      _ = (f : K) * (y : K) + 1 := by rw [hco]
      _ = _ := by ring
  exact ⟨⟨(a : K), hm⟩, NumberField.RingOfIntegers.coe_injective rfl⟩

/-- The genuine determinant norm is unchanged by inclusion from a
positive-conductor order into the maximal order. -/
theorem arithmeticSupply_conductor_norm_eq_maximal_norm (hf : 0 < f)
    (x : conductorOrder K f) :
    Algebra.norm ℤ x = Algebra.norm ℤ (conductorOrderToIntegers K f x) := by
  apply Int.cast_injective (α := ℚ)
  rw [← conductorOrder_norm_eq_field_norm K f hf x, Algebra.coe_norm_int]
  rfl

/-- Distinct genuine maximal-order principal ideals remain distinct
for their generators in the conductor order. -/
theorem arithmeticSupply_conductor_principal_distinct (a b : conductorOrder K f)
    (hne : Ideal.span ({conductorOrderToIntegers K f a} : Set (NumberField.RingOfIntegers K)) ≠
      Ideal.span ({conductorOrderToIntegers K f b} : Set (NumberField.RingOfIntegers K))) :
    Ideal.span ({a} : Set (conductorOrder K f)) ≠
      Ideal.span ({b} : Set (conductorOrder K f)) := by
  intro h
  apply hne
  have hm := congrArg (Ideal.map (conductorOrderToIntegers K f)) h
  simpa only [Ideal.map_span, Set.image_singleton] using hm

/-- Divisibility by a rational integer is reflected by the order inclusion
when that integer is coprime to the conductor. This is the injectivity part
of the reduction-modulo-p comparison in v3's supply proof. -/
theorem arithmeticSupply_conductor_divisibility_iff (hcop : Nat.Coprime p f)
    (x : conductorOrder K f) :
    (p : conductorOrder K f) ∣ x ↔
      (p : NumberField.RingOfIntegers K) ∣ conductorOrderToIntegers K f x := by
  constructor
  · intro hx
    simpa using map_dvd (conductorOrderToIntegers K f) hx
  · rintro ⟨y, hy⟩
    let A := p.gcdA f
    let B := p.gcdB f
    have hbez : (p : ℤ) * A + (f : ℤ) * B = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
      rfl
    have hbezK : (p : K) * (A : K) + (f : K) * (B : K) = 1 := by
      exact_mod_cast hbez
    have hyK : (x : K) = (p : K) * (y : K) := by
      have h := congrArg (fun z : NumberField.RingOfIntegers K => (z : K)) hy
      change (x : K) = (p : K) * (y : K) at h
      exact h
    let yO : conductorOrder K f := (A : conductorOrder K f) * x +
      integersMulConductor K f ((B : NumberField.RingOfIntegers K) * y)
    have hco : (yO : K) = (y : K) := by
      change (A : K) * (x : K) + (f : K) * ((B : K) * (y : K)) = (y : K)
      rw [hyK]
      calc
        _ = ((p : K) * (A : K) + (f : K) * (B : K)) * (y : K) := by ring
        _ = (y : K) := by rw [hbezK, one_mul]
    refine ⟨yO, Subtype.ext ?_⟩
    change (x : K) = (p : K) * (yO : K)
    rw [hco]
    exact hyK

/-- Every maximal-order residue class modulo a rational integer has a
conductor-order representative when the integer is coprime to the conductor.
This is the surjectivity part of the reduction comparison. -/
theorem arithmeticSupply_conductor_mod_lift (hcop : Nat.Coprime p f)
    (y : NumberField.RingOfIntegers K) :
    ∃ x : conductorOrder K f,
      (p : NumberField.RingOfIntegers K) ∣ y - conductorOrderToIntegers K f x := by
  let A := p.gcdA f
  let B := p.gcdB f
  have hbez : (p : ℤ) * A + (f : ℤ) * B = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have hbezK : (p : K) * (A : K) + (f : K) * (B : K) = 1 := by
    exact_mod_cast hbez
  refine ⟨integersMulConductor K f ((B : NumberField.RingOfIntegers K) * y),
    (A : NumberField.RingOfIntegers K) * y, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  change (y : K) - (f : K) * ((B : K) * (y : K)) =
    (p : K) * ((A : K) * (y : K))
  calc
    _ = ((p : K) * (A : K) + (f : K) * (B : K)) * (y : K) -
        (f : K) * ((B : K) * (y : K)) := by rw [hbezK, one_mul]
    _ = _ := by ring

/-- The actual ring map on reductions induced by the order inclusion. -/
def arithmeticSupply_conductorReductionMap :
    (conductorOrder K f ⧸ Ideal.span ({(p : conductorOrder K f)} : Set (conductorOrder K f))) →+*
      (NumberField.RingOfIntegers K ⧸
        Ideal.span ({(p : NumberField.RingOfIntegers K)} : Set (NumberField.RingOfIntegers K))) :=
  Ideal.quotientMap _ (conductorOrderToIntegers K f) (by
    intro x hx
    change conductorOrderToIntegers K f x ∈ Ideal.span ({(p : NumberField.RingOfIntegers K)} :
      Set (NumberField.RingOfIntegers K))
    rw [Ideal.mem_span_singleton] at hx ⊢
    simpa using map_dvd (conductorOrderToIntegers K f) hx)

theorem arithmeticSupply_conductorReductionMap_bijective (hcop : Nat.Coprime p f) :
    Function.Bijective (arithmeticSupply_conductorReductionMap K f p) := by
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.quotientMap _ (conductorOrderToIntegers K f) _ _ =
      Ideal.quotientMap _ (conductorOrderToIntegers K f) _ _ at h
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq,
      Ideal.mem_span_singleton, ← map_sub] at h
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact (arithmeticSupply_conductor_divisibility_iff K f p hcop (x - y)).mpr h
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := arithmeticSupply_conductor_mod_lift K f p hcop y
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    change Ideal.quotientMap _ (conductorOrderToIntegers K f) _ _ = _
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact (dvd_neg.mpr hx) |> (by simpa only [neg_sub] using ·)

/-- Away from the conductor, the actual order and maximal-order reductions
are isomorphic as unital rings. No index-f computation is assumed. -/
noncomputable def arithmeticSupply_conductorReductionEquiv (hcop : Nat.Coprime p f) :
    (conductorOrder K f ⧸ Ideal.span ({(p : conductorOrder K f)} : Set (conductorOrder K f))) ≃+*
      (NumberField.RingOfIntegers K ⧸
        Ideal.span ({(p : NumberField.RingOfIntegers K)} : Set (NumberField.RingOfIntegers K))) :=
  RingEquiv.ofBijective (arithmeticSupply_conductorReductionMap K f p)
    (arithmeticSupply_conductorReductionMap_bijective K f p hcop)

end ConductorReduction

section QuadraticProducts

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

/-- For the actual nonidentity quadratic automorphism, the product of two
conjugate order elements is the actual integer determinant norm. -/
theorem arithmeticSupply_conjugate_product_eq_norm
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (a b : conductorOrder K f) (hconj : (b : K) = τ (a : K)) :
    a * b = (Algebra.norm ℤ a : conductorOrder K f) := by
  classical
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  let g : Fin 2 → (K ≃ₐ[ℚ] K) := fun i => if i = 0 then AlgEquiv.refl else τ
  have hinj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have hc : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank ℚ K).trans hK
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hinj, by rw [Fintype.card_fin, hc]⟩)
  have h := field_norm_eq_product_embeddings (AlgHom.id ℚ K) e (a : K)
  simp [e, g] at h
  rw [conductorOrder_norm_eq_field_norm K f hf a] at h
  apply Subtype.ext
  change (a : K) * (b : K) = (Algebra.norm ℤ a : K)
  rw [hconj]
  exact_mod_cast h.symm

/-- Conjugate norm-prime generators have product associated to the
rational prime in the nonmaximal order itself. -/
theorem arithmeticSupply_conjugate_product_associated_prime
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (a b : conductorOrder K f) (hconj : (b : K) = τ (a : K))
    (p : ℕ) (hnorm : (Algebra.norm ℤ a).natAbs = p) :
    Associated (a * b) (p : conductorOrder K f) := by
  rw [arithmeticSupply_conjugate_product_eq_norm K f hK hf τ hτ a b hconj]
  have h : Associated (Algebra.norm ℤ a) (p : ℤ) :=
    Int.natAbs_eq_iff_associated.mp (by simpa only [Int.natAbs_natCast] using hnorm)
  simpa only [Int.coe_castRingHom, Int.cast_natCast] using
    h.map (Int.castRingHom (conductorOrder K f))

end QuadraticProducts

/-- Finite normal closures are already available in pinned mathlib. This
lemma makes that coverage explicit for any finite rational extension; the
existence of the required ray class extension is not asserted. -/
theorem arithmeticSupply_finite_normal_closure (E : Type*) [Field E] [CharZero E]
    [FiniteDimensional ℚ E] :
    FiniteDimensional ℚ (IntermediateField.normalClosure ℚ E (AlgebraicClosure E)) ∧
    Normal ℚ (IntermediateField.normalClosure ℚ E (AlgebraicClosure E)) ∧
    Nonempty (E →ₐ[ℚ] IntermediateField.normalClosure ℚ E (AlgebraicClosure E)) := by
  have : IsAlgClosure ℚ (AlgebraicClosure E) :=
    ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ E (AlgebraicClosure E)⟩
  have : Normal ℚ (AlgebraicClosure E) := IsAlgClosure.normal ℚ (AlgebraicClosure E)
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact ⟨IsScalarTower.toAlgHom ℚ E _⟩

end Entry002
