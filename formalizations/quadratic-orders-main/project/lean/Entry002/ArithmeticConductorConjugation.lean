import Entry002.ArithmeticSupplyElementary
import Entry002.PrimeSupply
import Entry002.ArithmeticPrimeIdealCounting

/-! Actual conductor automorphisms and the elementary assembly of residue
pairs. No density or prime generator existence is asserted. -/
set_option autoImplicit false
namespace Entry002
open scoped NumberField Pointwise

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

/-- Every field automorphism preserves the actual order ℤ + f O_K. -/
theorem arithmeticSupply_conductor_map_mem (τ : K ≃ₐ[ℚ] K)
    (x : K) (hx : x ∈ conductorOrder K f) : τ x ∈ conductorOrder K f := by
  obtain ⟨n, y, rfl⟩ := hx
  refine ⟨n, NumberField.RingOfIntegers.mapRingHom τ.toRingHom y, ?_⟩
  simp only [map_add, map_mul, map_intCast, map_natCast,
    NumberField.RingOfIntegers.mapRingHom_apply]
  rfl

/-- The actual induced ring automorphism of each conductor order. -/
def arithmeticSupply_conductorAutomorphism (τ : K ≃ₐ[ℚ] K) :
    conductorOrder K f ≃+* conductorOrder K f where
  toFun x := ⟨τ (x : K), arithmeticSupply_conductor_map_mem K f τ _ x.property⟩
  invFun x := ⟨τ.symm (x : K), arithmeticSupply_conductor_map_mem K f τ.symm _ x.property⟩
  left_inv x := by apply Subtype.ext; exact τ.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact τ.apply_symm_apply _
  map_mul' x y := by apply Subtype.ext; exact map_mul τ _ _
  map_add' x y := by apply Subtype.ext; exact map_add τ _ _

@[simp] theorem arithmeticSupply_conductorAutomorphism_coe (τ : K ≃ₐ[ℚ] K)
    (x : conductorOrder K f) :
    (arithmeticSupply_conductorAutomorphism K f τ x : K) = τ (x : K) := rfl

/-- Conjugation preserves the genuine integer determinant norm. -/
theorem arithmeticSupply_conductorAutomorphism_norm (τ : K ≃ₐ[ℚ] K)
    (x : conductorOrder K f) :
    Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ x) = Algebra.norm ℤ x :=
  Algebra.norm_eq_of_algEquiv (arithmeticSupply_conductorAutomorphism K f τ).toIntAlgEquiv x

/-- Genuine distinct conjugate norm-prime ideals yield the two surjective
unital residue maps and the exact intersection pO. -/
theorem arithmeticSupply_conjugate_residue_pair
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (p : ℕ) (hp : p.Prime) (a : conductorOrder K f)
    (hnorm : (Algebra.norm ℤ a).natAbs = p)
    (hdistinct : Ideal.span ({a} : Set (conductorOrder K f)) ≠
      Ideal.span ({arithmeticSupply_conductorAutomorphism K f τ a} : Set (conductorOrder K f))) :
    ∃ ψPlus ψMinus : conductorOrder K f →+* ZMod p,
      Function.Surjective ψPlus ∧ Function.Surjective ψMinus ∧
      (∀ x, ψPlus x = 0 ↔ a ∣ x) ∧
      (∀ x, ψMinus x = 0 ↔ arithmeticSupply_conductorAutomorphism K f τ a ∣ x) ∧
      ∀ x, (ψPlus x = 0 ∧ ψMinus x = 0) ↔ ∃ y, x = (p : ℤ) • y := by
  have hb : (Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ a)).natAbs = p := by
    rw [arithmeticSupply_conductorAutomorphism_norm]
    exact hnorm
  obtain ⟨ψPlus, hontoPlus, hkerPlus⟩ := arithmeticSupply_exists_normPrime_residueHom p hp a hnorm
  obtain ⟨ψMinus, hontoMinus, hkerMinus⟩ := arithmeticSupply_exists_normPrime_residueHom p hp
    (arithmeticSupply_conductorAutomorphism K f τ a) hb
  refine ⟨ψPlus, ψMinus, hontoPlus, hontoMinus, hkerPlus, hkerMinus, ?_⟩
  intro x
  rw [hkerPlus, hkerMinus]
  exact arithmeticSupply_pair_intersection p hp a
    (arithmeticSupply_conductorAutomorphism K f τ a) hnorm hb hdistinct
    (arithmeticSupply_conjugate_product_associated_prime K f hK hf τ hτ a _ rfl p hnorm) x

/-- At an unramified degree-one rational prime, every nonidentity Galois
automorphism moves the actual prime ideal. This uses the actual decomposition
group cardinality, not a supplied distinctness assertion. -/
theorem arithmeticSupply_split_prime_moved [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (he : P.ramificationIdx ℤ = 1) (hd : P.inertiaDeg ℤ = 1)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl) :
    τ • P ≠ P := by
  classical
  let : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have hcard := Ideal.card_stabilizer_eq (G := K ≃ₐ[ℚ] K)
    (Ideal.span {(p : ℤ)}) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (G := K ≃ₐ[ℚ] K) (Ideal.span {(p : ℤ)}) P,
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (K ≃ₐ[ℚ] K),
    he, hd, mul_one] at hcard
  let : Subsingleton (MulAction.stabilizer (K ≃ₐ[ℚ] K) P) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro hfixed
  have hm : τ ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) P := hfixed
  have hh : (⟨τ, hm⟩ : MulAction.stabilizer (K ≃ₐ[ℚ] K) P) = 1 := Subsingleton.elim _ _
  exact hτ (congrArg Subtype.val hh)

/-- The conjugate generator's maximal-order ideal is the actual Galois
translate of the original generator's ideal. -/
theorem arithmeticSupply_conductor_conjugate_ideal (τ : K ≃ₐ[ℚ] K)
    (a : conductorOrder K f) :
    Ideal.span ({conductorOrderToIntegers K f
      (arithmeticSupply_conductorAutomorphism K f τ a)} : Set (𝓞 K)) =
      τ • Ideal.span ({conductorOrderToIntegers K f a} : Set (𝓞 K)) := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
  congr 1

/-- A genuine principal degree-one unramified quadratic prime determines
both conjugate surjective residue maps and their exact paired kernel.
Distinctness, conjugate norm, and product association are proved here. -/
theorem arithmeticSupply_split_conductor_residue_pair
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (he : P.ramificationIdx ℤ = 1) (hd : P.inertiaDeg ℤ = 1)
    (a : conductorOrder K f)
    (hspan : Ideal.span ({conductorOrderToIntegers K f a} : Set (𝓞 K)) = P) :
    (Algebra.norm ℤ a).natAbs = p ∧
    (Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ a)).natAbs = p ∧
    ∃ ψPlus ψMinus : conductorOrder K f →+* ZMod p,
      Function.Surjective ψPlus ∧ Function.Surjective ψMinus ∧
      (∀ x, ψPlus x = 0 ↔ a ∣ x) ∧
      (∀ x, ψMinus x = 0 ↔ arithmeticSupply_conductorAutomorphism K f τ a ∣ x) ∧
      ∀ x, (ψPlus x = 0 ∧ ψMinus x = 0) ↔ ∃ y, x = (p : ℤ) • y := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hnorm : (Algebra.norm ℤ a).natAbs = p := by
    rw [arithmeticSupply_conductor_norm_eq_maximal_norm K f hf]
    exact arithmeticSupply_degree_one_generator_norm K p P hd
      (conductorOrderToIntegers K f a) hspan
  have hb : (Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ a)).natAbs = p := by
    rw [arithmeticSupply_conductorAutomorphism_norm]
    exact hnorm
  have hne : Ideal.span ({a} : Set (conductorOrder K f)) ≠
      Ideal.span ({arithmeticSupply_conductorAutomorphism K f τ a} : Set (conductorOrder K f)) := by
    apply arithmeticSupply_conductor_principal_distinct K f
    rw [arithmeticSupply_conductor_conjugate_ideal, hspan]
    exact (arithmeticSupply_split_prime_moved K p hp P he hd τ hτ).symm
  exact ⟨hnorm, hb, arithmeticSupply_conjugate_residue_pair K f hK hf τ hτ p hp a hnorm hne⟩

/-- A quadratic number field has a genuine nonidentity rational automorphism. -/
theorem arithmeticSupply_quadratic_nonidentity_automorphism
    (hK : Module.finrank ℚ K = 2) : ∃ τ : K ≃ₐ[ℚ] K, τ ≠ AlgEquiv.refl := by
  classical
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hc : Nat.card (K ≃ₐ[ℚ] K) = 2 := (IsGalois.card_aut_eq_finrank ℚ K).trans hK
  by_contra hnone
  have hτ : ∀ τ : K ≃ₐ[ℚ] K, τ = AlgEquiv.refl := by
    intro τ
    by_contra hne
    exact hnone ⟨τ, hne⟩
  have hs : Subsingleton (K ≃ₐ[ℚ] K) := ⟨fun x y => (hτ x).trans (hτ y).symm⟩
  have hcone : Nat.card (K ≃ₐ[ℚ] K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
  omega

end Entry002
