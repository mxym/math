import Mathlib

open scoped BigOperators
namespace ECQCCriticalRank

noncomputable section
variable (p : ℕ) [Fact p.Prime]

/-- The actual set of quadratic residues, including zero, in the prime field. -/
def residues : Finset (ZMod p) := Finset.univ.image (fun x => x^2)

theorem mem_residues (q : ZMod p) : q ∈ residues p ↔ ∃ x : ZMod p, x^2 = q := by
  simp [residues]

theorem zero_mem_residues : (0 : ZMod p) ∈ residues p :=
  (mem_residues p 0).mpr ⟨0, by ring⟩

theorem one_mem_residues : (1 : ZMod p) ∈ residues p :=
  (mem_residues p 1).mpr ⟨1, by ring⟩

theorem residue_scale (a : ZMod p) (ha : a ≠ 0) :
    (residues p).image (fun q => a^2*q) = residues p := by
  ext q
  constructor
  · intro hq
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨x,rfl⟩ := (mem_residues p r).mp hr
    exact (mem_residues p _).mpr ⟨a*x, by ring⟩
  · intro hq
    obtain ⟨x,rfl⟩ := (mem_residues p q).mp hq
    apply Finset.mem_image.mpr
    refine ⟨(a⁻¹*x)^2, (mem_residues p _).mpr ⟨a⁻¹*x,rfl⟩, ?_⟩
    field_simp

theorem residue_sum_zero (hp : 5 ≤ p) :
    ∑ q ∈ residues p, q = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hd
    omega
  have hscale := residue_scale p 2 h2
  have hinj : ∀ x ∈ residues p, ∀ y ∈ residues p,
      (2 : ZMod p)^2*x = 2^2*y → x = y := by
    intro x _ y _ h
    exact mul_left_cancel₀ (pow_ne_zero _ h2) h
  have hs : (2 : ZMod p)^2 * (∑ q ∈ residues p, q) = ∑ q ∈ residues p, q := by
    rw [Finset.mul_sum]
    calc
      (∑ q ∈ residues p, (2 : ZMod p)^2*q) =
          ∑ q ∈ (residues p).image (fun q => (2 : ZMod p)^2*q), q :=
        (Finset.sum_image (f := fun q : ZMod p => q) hinj).symm
      _ = ∑ q ∈ residues p, q := by rw [hscale]
  have hz : (3 : ZMod p) * (∑ q ∈ residues p, q) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left h3

theorem residues_proper (hp : 3 ≤ p) : residues p ≠ Finset.univ := by
  intro he
  have hsurj : Function.Surjective (fun x : ZMod p => x^2) := by
    intro q
    exact (mem_residues p q).mp (by rw [he]; exact Finset.mem_univ q)
  have hinj := (Finite.injective_iff_surjective).mpr hsurj
  have hm : (1 : ZMod p) = -1 := hinj (by ring)
  have hz : (2 : ZMod p) = 0 := by linear_combination hm
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
  omega

theorem residue_card_nonzero (hp : 3 ≤ p) : ((residues p).card : ZMod p) ≠ 0 := by
  have hpos : 0 < (residues p).card := Finset.card_pos.mpr ⟨0, zero_mem_residues p⟩
  have hlt : (residues p).card < p := by
    have hproper : residues p ⊂ Finset.univ :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ _, residues_proper p hp⟩
    have h := Finset.card_lt_card hproper
    simpa only [Finset.card_univ, ZMod.card] using h
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ p).mp hz
  have := Nat.le_of_dvd hpos hd
  omega

/-- The finite-field obstruction used after the actual reduced Fourier argument.
It concerns the full residue set, not a finite list of tested primes. -/
theorem residue_reflection_forces_square_neg_one (hp : 5 ≤ p)
    (σ : {q : ZMod p // q ∈ residues p} ≃ {q : ZMod p // q ∈ residues p})
    (κ : ZMod p) (hκ : ∀ q, q.val + (σ q).val = κ) :
    κ = 0 ∧ ∃ s : ZMod p, s^2 = -1 := by
  have hs : (∑ q : {q : ZMod p // q ∈ residues p}, q.val) = 0 := by
    exact (Finset.sum_subtype (residues p) (fun _ => Iff.rfl)
      (fun q : ZMod p => q)).symm.trans (residue_sum_zero p hp)
  have hσ : (∑ q : {q : ZMod p // q ∈ residues p}, (σ q).val) = 0 := by
    rw [Equiv.sum_comp σ]
    exact hs
  have he : ((residues p).card : ZMod p)*κ = 0 := by
    have hh := Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => hκ q)
    simp only [Finset.sum_add_distrib, hs, hσ, add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hh
    exact hh.symm
  have hk : κ = 0 := (mul_eq_zero.mp he).resolve_left (residue_card_nonzero p (by omega))
  refine ⟨hk, ?_⟩
  let oneQ : {q : ZMod p // q ∈ residues p} := ⟨1, one_mem_residues p⟩
  have hv : (σ oneQ).val = -1 := by
    have hh := hκ oneQ
    rw [hk] at hh
    change 1 + (σ oneQ).val = 0 at hh
    linear_combination hh
  exact (mem_residues p (-1)).mp (hv ▸ (σ oneQ).property)

/-- No residue reflection can occur in the obstructed congruence class. -/
theorem no_residue_reflection_mod_four_three (hp : 5 ≤ p) (hmod : p % 4 = 3)
    (σ : {q : ZMod p // q ∈ residues p} ≃ {q : ZMod p // q ∈ residues p})
    (κ : ZMod p) (hκ : ∀ q, q.val + (σ q).val = κ) : False := by
  obtain ⟨_,s,hs⟩ := residue_reflection_forces_square_neg_one p hp σ κ hκ
  have hsq : IsSquare (-1 : ZMod p) := ⟨s, by rw [← hs, pow_two]⟩
  exact ZMod.exists_sq_eq_neg_one_iff.mp hsq hmod

#print axioms residue_reflection_forces_square_neg_one
#print axioms no_residue_reflection_mod_four_three
end
end ECQCCriticalRank
