import Entry002.ArithmeticInterface
import Entry002.Embedding
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic
import Entry002.ArithmeticCore
import Entry002.GenericSignedArithmetic

/-! Core-only replay of the round-five owned `GenericSignedArithmetic` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Basis-independent signed-kernel arithmetic for the A1--A5 sieve interface.
The determinant is the actual integral coefficient determinant. No ring
structure, Gaussian factorization, or replacement notion of primitiveness is
required on the rank-two lattice. -/

namespace Entry002.WeakA5

open Module
open scoped BigOperators

variable {L : Type*} [AddCommGroup L]

/-- The integer determinant in the supplied genuine integral lattice basis. -/
def latticeDet (b : Basis (Fin 2) ℤ L) (x y : L) : ℤ :=
  b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0

/-- The joint selected residue map, as an actual additive homomorphism. -/
def selectedResidueMap (data : SignedResidueData L) (S : Finset ℕ)
    (σ : ℕ → Bool) : L →+ (∀ p : S, ZMod p.val) where
  toFun x p := data.phi p.val (σ p.val) x
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _

/-- The exact A1 common-kernel index, derived from actual surjectivity and the
first isomorphism theorem rather than supplied as a premise. -/
theorem selected_kernel_index (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (σ : ℕ → Bool) :
    (selectedResidueMap data S σ).ker.index = S.prod id := by
  classical
  calc
    _ = Nat.card (L ⧸ (selectedResidueMap data S σ).ker) := AddSubgroup.index_eq_card _
    _ = Nat.card (∀ p : S, ZMod p.val) := Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective (selectedResidueMap data S σ)
        (signedResidueData_crt data S hS σ)).toEquiv
    _ = ∏ p : S, p.val := by simp only [Nat.card_pi, Nat.card_zmod]
    _ = S.prod id := Finset.prod_coe_sort S id

theorem primitive_coefficients_coprime (b : Basis (Fin 2) ℤ L) {v : L}
    (hv : IsPrimitive v) : IsCoprime (b.repr v 0) (b.repr v 1) := by
  have hg : 0 < Int.gcd (b.repr v 0) (b.repr v 1) := by
    apply Nat.pos_of_ne_zero
    intro hn
    obtain ⟨h₀, h₁⟩ := Int.gcd_eq_zero_iff.mp hn
    apply hv.1
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [h₀, h₁]
  obtain ⟨m, n, hcop, hm, hn⟩ := Int.exists_gcd_one hg
  let w : L := m • b 0 + n • b 1
  have he : v = (Int.gcd (b.repr v 0) (b.repr v 1) : ℤ) • w := by
    apply b.repr.injective
    ext i
    fin_cases i
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr v 0 = (Int.gcd (b.repr v 0) (b.repr v 1) : ℤ) * b.repr w 0
      have hw : b.repr w 0 = m := by simp [w]
      rw [hw]
      exact hm.trans (mul_comm _ _)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr v 1 = (Int.gcd (b.repr v 0) (b.repr v 1) : ℤ) * b.repr w 1
      have hw : b.repr w 1 = n := by simp [w]
      rw [hw]
      exact hn.trans (mul_comm _ _)
  have hgle : Int.gcd (b.repr v 0) (b.repr v 1) ≤ 1 := by
    by_contra h
    have hgt : 1 < (Int.gcd (b.repr v 0) (b.repr v 1) : ℤ) := by
      exact_mod_cast (lt_of_not_ge h)
    exact hv.2 _ w (by simpa using hgt) he
  exact Int.isCoprime_iff_gcd_eq_one.mpr (Nat.le_antisymm hgle hg)

theorem primitive_of_coefficients_coprime (b : Basis (Fin 2) ℤ L) {v : L}
    (hv : IsCoprime (b.repr v 0) (b.repr v 1)) : IsPrimitive v := by
  constructor
  · intro he
    obtain ⟨r, s, hrs⟩ := hv
    simp [he] at hrs
  · intro a w ha he
    have hc (i : Fin 2) : b.repr v i = a * b.repr w i := by
      rw [he]
      simp
    have hu : IsUnit a := hv.isUnit_of_dvd' ⟨b.repr w 0, hc 0⟩ ⟨b.repr w 1, hc 1⟩
    obtain rfl | rfl := Int.isUnit_iff.mp hu <;> norm_num at ha

/-- Every nonzero integral lattice vector has an actual primitive direction. -/
theorem exists_primitive_lattice_direction (b : Basis (Fin 2) ℤ L) {w : L}
    (hw : w ≠ 0) : ∃ v : L, IsPrimitive v ∧ ∃ a : ℤ, a ≠ 0 ∧ w = a • v := by
  have hg : 0 < Int.gcd (b.repr w 0) (b.repr w 1) := by
    apply Nat.pos_of_ne_zero
    intro hn
    obtain ⟨h₀, h₁⟩ := Int.gcd_eq_zero_iff.mp hn
    apply hw
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [h₀, h₁]
  obtain ⟨m, n, hcop, hm, hn⟩ := Int.exists_gcd_one hg
  let v : L := m • b 0 + n • b 1
  refine ⟨v, primitive_of_coefficients_coprime b ?_,
    (Int.gcd (b.repr w 0) (b.repr w 1) : ℤ), by exact_mod_cast hg.ne', ?_⟩
  · simpa [v] using Int.isCoprime_iff_gcd_eq_one.mpr hcop
  · apply b.repr.injective
    ext i
    fin_cases i
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr w 0 = (Int.gcd (b.repr w 0) (b.repr w 1) : ℤ) * b.repr v 0
      have hv : b.repr v 0 = m := by simp [v]
      rw [hv]
      exact hm.trans (mul_comm _ _)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr w 1 = (Int.gcd (b.repr w 0) (b.repr w 1) : ℤ) * b.repr v 1
      have hv : b.repr v 1 = n := by simp [v]
      rw [hv]
      exact hn.trans (mul_comm _ _)

/-- Collinear vectors are integer multiples of an actual primitive lattice
direction; the integer coefficient is given by Bézout. -/
theorem integer_multiple_of_latticeDet_zero (b : Basis (Fin 2) ℤ L) {v w : L}
    (hv : IsPrimitive v) (hd : latticeDet b v w = 0) : ∃ a : ℤ, w = a • v := by
  obtain ⟨r, s, hrs⟩ := primitive_coefficients_coprime b hv
  refine ⟨r * b.repr w 0 + s * b.repr w 1, ?_⟩
  apply b.repr.injective
  ext i
  fin_cases i
  · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    change b.repr w 0 = (r * b.repr w 0 + s * b.repr w 1) * b.repr v 0
    dsimp [latticeDet] at hd
    nlinarith [congrArg (fun z : ℤ => z * b.repr w 0) hrs,
      congrArg (fun z : ℤ => s * z) hd]
  · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    change b.repr w 1 = (r * b.repr w 0 + s * b.repr w 1) * b.repr v 1
    dsimp [latticeDet] at hd
    nlinarith [congrArg (fun z : ℤ => z * b.repr w 1) hrs,
      congrArg (fun z : ℤ => r * z) hd]

theorem primitive_not_both_signed_kernels (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticCore data b e) {p : ℕ} (hp : p ∈ data.primes)
    {v : L} (hv : IsPrimitive v) :
    ¬ (data.phi p true v = 0 ∧ data.phi p false v = 0) := by
  intro h
  obtain ⟨w, hw⟩ := (hA.paired_kernel p hp v).mp h
  exact hv.2 (p : ℤ) w
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg p)] using
      (show (1 : ℤ) < p by exact_mod_cast (data.prime_mem p hp).one_lt)) hw

/-- Every additive residue map is given by its two basis-coordinate values. -/
theorem residue_basis_expansion (b : Basis (Fin 2) ℤ L) {p : ℕ}
    (φ : L →+ ZMod p) (x : L) :
    φ x = (b.repr x 0 : ZMod p) * φ (b 0) + (b.repr x 1 : ZMod p) * φ (b 1) := by
  have hx : x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  calc
    φ x = φ ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) := congrArg φ hx
    _ = _ := by rw [map_add, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]

/-- A surjective map onto a prime residue field cannot vanish on both basis
vectors. -/
theorem residue_basis_nonzero (b : Basis (Fin 2) ℤ L) {p : ℕ}
    (hp : Nat.Prime p) (φ : L →+ ZMod p) (honto : Function.Surjective φ) :
    φ (b 0) ≠ 0 ∨ φ (b 1) ≠ 0 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  by_contra hn
  push Not at hn
  obtain ⟨x, hx⟩ := honto 1
  have he := residue_basis_expansion b φ x
  rw [hn.1, hn.2, mul_zero, mul_zero, add_zero, hx] at he
  exact one_ne_zero he

/-- Two vectors in a single prime kernel have determinant divisible by that
prime. This replaces the Gaussian common-factor norm identity. -/
theorem residue_kernel_dvd_latticeDet (b : Basis (Fin 2) ℤ L) {p : ℕ}
    (hp : Nat.Prime p) (φ : L →+ ZMod p) (honto : Function.Surjective φ)
    {x y : L} (hx : φ x = 0) (hy : φ y = 0) : (p : ℤ) ∣ latticeDet b x y := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (latticeDet b x y) p).mp
  have h₀ : φ (b 0) * (latticeDet b x y : ZMod p) = 0 := by
    have he₀ := (residue_basis_expansion b φ x).symm.trans hx
    have he₁ := (residue_basis_expansion b φ y).symm.trans hy
    simp only [latticeDet, Int.cast_sub, Int.cast_mul]
    linear_combination (b.repr y 1 : ZMod p) * he₀ - (b.repr x 1 : ZMod p) * he₁
  have h₁ : φ (b 1) * (latticeDet b x y : ZMod p) = 0 := by
    have he₀ := (residue_basis_expansion b φ x).symm.trans hx
    have he₁ := (residue_basis_expansion b φ y).symm.trans hy
    simp only [latticeDet, Int.cast_sub, Int.cast_mul]
    linear_combination (b.repr x 0 : ZMod p) * he₁ - (b.repr y 0 : ZMod p) * he₀
  rcases residue_basis_nonzero b hp φ honto with h | h
  · exact (mul_eq_zero.mp h₀).resolve_left h
  · exact (mul_eq_zero.mp h₁).resolve_left h

/-- The exact product of common selected primes divides the integral
determinant. All maps may merely be additive. -/
theorem selected_kernel_product_dvd_latticeDet (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (σ : ℕ → Bool) {x y : L}
    (hx : ∀ p ∈ S, data.phi p (σ p) x = 0)
    (hy : ∀ p ∈ S, data.phi p (σ p) y = 0) :
    (∏ p ∈ S, (p : ℤ)) ∣ latticeDet b x y := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (Nat.coprime_primes (data.prime_mem p (hS p hp))
      (data.prime_mem q (hS q hq))).mpr hpq
  · intro p hp
    exact residue_kernel_dvd_latticeDet b (data.prime_mem p (hS p hp))
      (data.phi p (σ p)) (data.onto p (hS p hp) (σ p)) (hx p hp) (hy p hp)

/-- On a line, a selected map which does not kill the direction kills the
integer multiple precisely when its prime divides the integer coefficient. -/
theorem residue_zsmul_zero_iff {p : ℕ} (hp : Nat.Prime p)
    (φ : L →+ ZMod p) {v : L} (hv : φ v ≠ 0) (a : ℤ) :
    φ (a • v) = 0 ↔ (p : ℤ) ∣ a := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  rw [map_zsmul, zsmul_eq_mul, mul_eq_zero]
  simpa only [hv, or_false] using ZMod.intCast_zmod_eq_zero_iff_dvd a p

/-- Exact divisibility of the integer line coefficient by all uneligible
selected primes. This needs no primality notion on lattice elements. -/
theorem uneligible_product_dvd_coefficient (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (σ : ℕ → Bool)
    (v : L) (a : ℤ) (hw : ∀ p ∈ S, data.phi p (σ p) (a • v) = 0) :
    (∏ p ∈ S.filter (fun p => data.phi p (σ p) v ≠ 0), (p : ℤ)) ∣ a := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (Nat.coprime_primes (data.prime_mem p (hS p (Finset.mem_filter.mp hp).1))
      (data.prime_mem q (hS q (Finset.mem_filter.mp hq).1))).mpr hpq
  · intro p hp
    obtain ⟨hpS, hpv⟩ := Finset.mem_filter.mp hp
    exact (residue_zsmul_zero_iff (data.prime_mem p (hS p hpS))
      (data.phi p (σ p)) hpv a).mp (hw p hpS)

@[simp] theorem planarEmbedding_zsmul_signed (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (a : ℤ) (v : L) :
    planarEmbedding b e (a • v) = (a : ℝ) • planarEmbedding b e v := by
  unfold planarEmbedding
  rw [← e.map_smul]
  congr 1
  funext i
  simp

@[simp] theorem planarEmbedding_sub_signed (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : L) :
    planarEmbedding b e (x - y) = planarEmbedding b e x - planarEmbedding b e y := by
  unfold planarEmbedding
  have hc : (fun i => (b.repr (x - y) i : ℝ)) =
      (fun i => (b.repr x i : ℝ)) - (fun i => (b.repr y i : ℝ)) := by
    funext i
    simp
  rw [hc]
  exact e.map_sub _ _

/-- A3 makes every selected residue map injective on any set of sufficiently
small diameter. Both distances and collisions use the actual planar embedding. -/
theorem residue_injective_at_collision_scale (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hA : ArithmeticCore data b e) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ data.primes, ∀ s : Bool, ∀ x y : L,
      ‖planarEmbedding b e x - planarEmbedding b e y‖ < c * Real.sqrt (p : ℝ) →
      data.phi p s x = data.phi p s y → x = y := by
  obtain ⟨c, hc, hcollision⟩ := hA.collision
  refine ⟨c, hc, ?_⟩
  intro p hp s x y hshort hres
  by_contra hne
  have hzero : data.phi p s (x - y) = 0 := by simp [hres]
  have hlo := hcollision p hp s (x - y) (sub_ne_zero.mpr hne) hzero
  rw [planarEmbedding_sub_signed] at hlo
  linarith

/-- The exact line-witness length lower bound used before taking logarithms
in the thin-rectangle separation lemma. This is the actual planar norm. -/
theorem line_witness_length_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (σ : ℕ → Bool)
    {v w : L} (hv : IsPrimitive v) (hw : w ≠ 0) (hline : latticeDet b v w = 0)
    (hker : ∀ p ∈ S, data.phi p (σ p) w = 0) :
    ‖planarEmbedding b e v‖ *
      (∏ p ∈ S.filter (fun p => data.phi p (σ p) v ≠ 0), (p : ℝ)) ≤
        ‖planarEmbedding b e w‖ := by
  classical
  obtain ⟨a, rfl⟩ := integer_multiple_of_latticeDet_zero b hv hline
  have ha : a ≠ 0 := by intro h; simp [h] at hw
  have hd := uneligible_product_dvd_coefficient data S hS σ v a hker
  have hle := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hd)
  have hc : (((∏ p ∈ S.filter (fun p => data.phi p (σ p) v ≠ 0), (p : ℤ)) : ℤ) : ℝ)
      ≤ ((|a| : ℤ) : ℝ) := Int.cast_le.mpr hle
  have hp : (∏ p ∈ S.filter (fun p => data.phi p (σ p) v ≠ 0), (p : ℝ)) ≤ |(a : ℝ)| := by
    simpa only [Int.cast_prod, Int.cast_natCast, Int.cast_abs] using hc
  calc
    _ ≤ ‖planarEmbedding b e v‖ * |(a : ℝ)| :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖planarEmbedding b e (a • v)‖ := by rw [planarEmbedding_zsmul_signed, norm_smul, Real.norm_eq_abs, mul_comm]

/-- The number of changed coordinates on the selected prime set. -/
noncomputable def selectedSignDistance (S : Finset ℕ) (σ τ : ℕ → Bool) : ℕ := by
  classical
  exact (S.filter (fun p => σ p ≠ τ p)).card

/-- Removing the changed signs loses at most one factor `U` per change. -/
theorem period_le_common_product (S : Finset ℕ) (σ τ : ℕ → Bool) {U : ℝ}
    (hpU : ∀ p ∈ S, (p : ℝ) ≤ U) :
    (∏ p ∈ S, (p : ℝ)) ≤
      (∏ p ∈ S.filter (fun p => σ p = τ p), (p : ℝ)) * U ^ selectedSignDistance S σ τ := by
  classical
  let c := S.filter (fun p => σ p = τ p)
  let d := S.filter (fun p => σ p ≠ τ p)
  have hd : (∏ p ∈ d, (p : ℝ)) ≤ U ^ d.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
      (fun p hp => hpU p (Finset.mem_filter.mp hp).1)
  have he : (∏ p ∈ S, (p : ℝ)) =
      (∏ p ∈ c, (p : ℝ)) * (∏ p ∈ d, (p : ℝ)) :=
    (Finset.prod_filter_mul_prod_filter_not S (fun p => σ p = τ p)
      (fun p => (p : ℝ))).symm
  rw [he]
  exact mul_le_mul_of_nonneg_left hd (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p))

/-- A nonzero determinant of common-kernel witnesses is at least the exact
common prime product. -/
theorem common_product_le_abs_det (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (σ τ : ℕ → Bool) {x y : L}
    (hx : ∀ p ∈ S, data.phi p (σ p) x = 0)
    (hy : ∀ p ∈ S, data.phi p (τ p) y = 0) (hdet : latticeDet b x y ≠ 0) :
    (∏ p ∈ S.filter (fun p => σ p = τ p), (p : ℝ)) ≤ |(latticeDet b x y : ℝ)| := by
  classical
  have hd := selected_kernel_product_dvd_latticeDet data b
    (S.filter (fun p => σ p = τ p))
    (fun p hp => hS p (Finset.mem_filter.mp hp).1) σ
    (fun p hp => hx p (Finset.mem_filter.mp hp).1)
    (fun p hp => by rw [(Finset.mem_filter.mp hp).2]; exact hy p (Finset.mem_filter.mp hp).1)
  have hle := Int.le_of_dvd (abs_pos.mpr hdet) ((dvd_abs _ _).mpr hd)
  have hcast : (((∏ p ∈ S.filter (fun p => σ p = τ p), (p : ℤ)) : ℤ) : ℝ) ≤
      ((|latticeDet b x y| : ℤ) : ℝ) := Int.cast_le.mpr hle
  simpa only [Int.cast_prod, Int.cast_natCast, Int.cast_abs] using hcast

/-- The arithmetic separation step in the thin-rectangle proof: witnesses
whose signs differ in few coordinates must be collinear when the determinant
window is smaller than the exact common-kernel index. -/
theorem near_kernel_witnesses_collinear (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (σ τ : ℕ → Bool) {x y : L}
    (hx : ∀ p ∈ S, data.phi p (σ p) x = 0)
    (hy : ∀ p ∈ S, data.phi p (τ p) y = 0) {U B : ℝ}
    (hU : 0 < U) (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hdet : |(latticeDet b x y : ℝ)| ≤ B)
    (hsmall : B * U ^ selectedSignDistance S σ τ < ∏ p ∈ S, (p : ℝ)) :
    latticeDet b x y = 0 := by
  by_contra hn
  have hcom := common_product_le_abs_det data b S hS σ τ hx hy hn
  have hlo := period_le_common_product S σ τ hpU
  have hlt : B < ∏ p ∈ S.filter (fun p => σ p = τ p), (p : ℝ) := by
    apply (mul_lt_mul_iff_left₀ (pow_pos hU _)).mp
    simpa only [mul_comm] using hsmall.trans_le hlo
  linarith

/-- The real signed area in the actual Euclidean-plane coordinates. -/
def signedPlaneDet (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

/-- The signed area of a fundamental cell of the given full planar lattice. -/
def planarCellDet (e : CoeffSpace ≃ₗ[ℝ] Plane) : ℝ :=
  signedPlaneDet (e (Pi.single 0 1)) (e (Pi.single 1 1))

theorem planarCellDet_ne_zero (e : CoeffSpace ≃ₗ[ℝ] Plane) : planarCellDet e ≠ 0 := by
  let q : CoeffSpace ≃ₗ[ℝ] CoeffSpace :=
    e.trans (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv
  have hn := (q.isUnit_det (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))).ne_zero
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr] at hn
  change (e (Pi.single 0 1)) 0 * (e (Pi.single 1 1)) 1 -
    (e (Pi.single 1 1)) 0 * (e (Pi.single 0 1)) 1 ≠ 0 at hn
  simpa only [planarCellDet, signedPlaneDet, mul_comm] using hn

theorem planarEmbedding_column_expansion (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x : L) :
    planarEmbedding b e x = (b.repr x 0 : ℝ) • e (Pi.single 0 1) +
      (b.repr x 1 : ℝ) • e (Pi.single 1 1) := by
  have hx : (fun i => (b.repr x i : ℝ)) =
      (b.repr x 0 : ℝ) • Pi.single 0 1 + (b.repr x 1 : ℝ) • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  unfold planarEmbedding
  rw [hx, map_add, map_smul, map_smul]

/-- Exact conversion from coefficient determinant to Euclidean signed area,
including the actual lattice covolume factor. -/
theorem planarEmbedding_determinant (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : L) :
    signedPlaneDet (planarEmbedding b e x) (planarEmbedding b e y) =
      (latticeDet b x y : ℝ) * planarCellDet e := by
  rw [planarEmbedding_column_expansion b e x, planarEmbedding_column_expansion b e y]
  simp only [signedPlaneDet, planarCellDet, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, latticeDet, Int.cast_sub, Int.cast_mul]
  ring

/-- The rectangle is measured in actual planar coordinates, after any chosen
orientation isometry. -/
def latticeRectangle (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (o : Plane ≃ₗᵢ[ℝ] Plane) (R W : ℝ) : Set L :=
  {x | |o (planarEmbedding b e x) 0| ≤ R ∧ |o (planarEmbedding b e x) 1| ≤ W}

theorem latticeRectangle_norm_bound (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) {R W : ℝ}
    (hW : 0 ≤ W) (hWR : W ≤ R) {x : L} (hx : x ∈ latticeRectangle b e o R W) :
    ‖planarEmbedding b e x‖ ^ 2 ≤ 2 * R ^ 2 := by
  have h₀ : (o (planarEmbedding b e x) 0) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (hW.trans hWR)).mpr hx.1
  have h₁ : (o (planarEmbedding b e x) 1) ^ 2 ≤ W ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hW).mpr hx.2
  have hsq : W ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hW (hW.trans hWR)).mpr hWR
  have hn := EuclideanSpace.real_norm_sq_eq (o (planarEmbedding b e x))
  simp only [Fin.sum_univ_two, o.norm_map] at hn
  nlinarith

/-- Thin rectangle area controls the genuine coefficient determinant, with
the fundamental-cell area accounted for explicitly. -/
theorem latticeRectangle_determinant_bound (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane)
    {R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W) {x y : L}
    (hx : x ∈ latticeRectangle b e o R W) (hy : y ∈ latticeRectangle b e o R W) :
    |(latticeDet b x y : ℝ)| ≤ 2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)| := by
  have hc : 0 < |planarCellDet (e.trans o.toLinearEquiv)| :=
    abs_pos.mpr (planarCellDet_ne_zero _)
  apply (le_div_iff₀ hc).mpr
  have he := congrArg abs (planarEmbedding_determinant b (e.trans o.toLinearEquiv) x y)
  rw [abs_mul] at he
  rw [← he]
  change |o (planarEmbedding b e x) 0 * o (planarEmbedding b e y) 1 -
    o (planarEmbedding b e x) 1 * o (planarEmbedding b e y) 0| ≤ 2 * R * W
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have h₀ := mul_le_mul hx.1 hy.2 (abs_nonneg _) hR
  have h₁ := mul_le_mul hx.2 hy.1 (abs_nonneg _) hW
  nlinarith

/-- The complete deterministic thin-rectangle sign-separation step. -/
theorem nearby_rectangle_kernel_witnesses_collinear (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (o : Plane ≃ₗᵢ[ℝ] Plane) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (σ τ : ℕ → Bool) {x y : L} {R W U : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hx : x ∈ latticeRectangle b e o R W) (hy : y ∈ latticeRectangle b e o R W)
    (hxker : ∀ p ∈ S, data.phi p (σ p) x = 0)
    (hyker : ∀ p ∈ S, data.phi p (τ p) y = 0) (hU : 0 < U)
    (hpU : ∀ p ∈ S, (p : ℝ) ≤ U)
    (hsmall : (2 * R * W / |planarCellDet (e.trans o.toLinearEquiv)|) *
      U ^ selectedSignDistance S σ τ < ∏ p ∈ S, (p : ℝ)) : latticeDet b x y = 0 :=
  near_kernel_witnesses_collinear data b S hS σ τ hxker hyker hU hpU
    (latticeRectangle_determinant_bound b e o hR hW hx hy) hsmall

end Entry002.WeakA5
