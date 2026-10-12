import BapatFiniteRankEndpoint
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
open scoped BigOperators
open BapatRankTwo.MarkedInversions

namespace BapatFiniteRank

section Products

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]

def deleteTwoProduct (f : ι → M) (i j : ι) : M :=
  ∏ k ∈ (Finset.univ.erase i).erase j, f k

theorem deleteTwoProduct_ite (f : ι → M) (i j : ι) :
    deleteTwoProduct f i j = ∏ k, if k ≠ i ∧ k ≠ j then f k else 1 := by
  have hs : (Finset.univ.erase i).erase j =
      Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) := by
    ext k
    simp [and_comm]
  rw [deleteTwoProduct, hs, Finset.prod_filter]

theorem product_split_two (f : ι → M) {i j : ι} (hij : i ≠ j) :
    (∏ k, f k) = f i * f j * deleteTwoProduct f i j := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) f
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  simp only [deleteTwoProduct, mul_assoc]

theorem repeat_deleteTwoProduct (f : ι → M) {L : ℕ} (hL : 0 < L)
    {i j : ι} (hij : i ≠ j) (a b : Fin L) :
    deleteTwoProduct (fun p : ι × Fin L => f p.1) (i,a) (j,b) =
      (∏ k, f k) ^ (L-1) * deleteTwoProduct f i j := by
  rw [deleteTwoProduct_ite, Fintype.prod_prod_type]
  have hi : (∏ c : Fin L,
      if (i,c) ≠ (i,a) ∧ (i,c) ≠ (j,b) then f i else 1) = f i ^ (L-1) := by
    simp only [ne_eq, Prod.mk.injEq, true_and, hij, false_and, not_false_eq_true,
      and_true, eq_self_iff_true]
    rw [← Finset.prod_filter]
    have hs : Finset.univ.filter (fun c : Fin L => c ≠ a) = Finset.univ.erase a := by
      ext c; simp
    rw [hs]
    simp
  have hj : (∏ c : Fin L,
      if (j,c) ≠ (i,a) ∧ (j,c) ≠ (j,b) then f j else 1) = f j ^ (L-1) := by
    simp only [ne_eq, Prod.mk.injEq, true_and, hij.symm, false_and, not_false_eq_true,
      eq_self_iff_true]
    rw [← Finset.prod_filter]
    have hs : Finset.univ.filter (fun c : Fin L => c ≠ b) = Finset.univ.erase b := by
      ext c; simp
    rw [hs]
    simp
  rw [product_split_two (fun k => ∏ c : Fin L,
    if (k,c) ≠ (i,a) ∧ (k,c) ≠ (j,b) then f k else 1) hij, hi, hj]
  have ho : deleteTwoProduct (fun k => ∏ c : Fin L,
      if (k,c) ≠ (i,a) ∧ (k,c) ≠ (j,b) then f k else 1) i j =
      (deleteTwoProduct f i j)^L := by
    unfold deleteTwoProduct
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    simp [Prod.mk.injEq, hki, hkj]
  rw [ho, product_split_two f hij, mul_pow, mul_pow]
  have hpow : (deleteTwoProduct f i j)^L =
      (deleteTwoProduct f i j)^(L-1) * deleteTwoProduct f i j := by
    rw [← pow_succ, Nat.sub_add_cancel hL]
  rw [hpow]
  ac_rfl

end Products

section Reindexing

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ] [CommMonoid M]

theorem deleteTwoProduct_comp (e : ι ≃ κ) (f : κ → M) (i j : ι) :
    deleteTwoProduct (fun x => f (e x)) i j = deleteTwoProduct f (e i) (e j) := by
  simp only [deleteTwoProduct_ite]
  simpa using e.prod_comp (fun k => if k ≠ e i ∧ k ≠ e j then f k else 1)

end Reindexing

section LexSums

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommSemiring R]

theorem sum_lex_prod {L : ℕ} (f : ι ×ₗ Fin L → R) :
    (∑ p, f p) = ∑ i, ∑ a : Fin L, f (toLex (i,a)) := by
  rw [← Fintype.sum_prod_type (fun p : ι × Fin L => f (toLex p))]
  exact (toLex.sum_comp f).symm

/-- Contiguity is encoded by the lexicographic order: same-block terms vanish,
and each ordered distinct block pair occurs exactly L squared times. -/
theorem repeated_pair_sum (g : ι → ι → R) (hg : ∀ i, g i i = 0) (L : ℕ) :
    (∑ p ∈ originalPairs (ι := ι ×ₗ Fin L), g (ofLex p.1).1 (ofLex p.2).1) =
      (L : R)^2 * ∑ p ∈ originalPairs (ι := ι), g p.1 p.2 := by
  classical
  simp only [originalPairs, Finset.sum_filter, Fintype.sum_prod_type]
  rw [sum_lex_prod]
  simp_rw [sum_lex_prod, Prod.Lex.toLex_lt_toLex, ofLex_toLex]
  have ht : ∀ (i j : ι) (a b : Fin L),
      (if i < j ∨ i = j ∧ a < b then g i j else 0) =
      if i < j then g i j else 0 := by
    intro i j a b
    by_cases h : i = j
    · subst j
      simp [hg]
    · simp [h]
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  ring

end LexSums

section Polynomials

variable {ι C R : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype C] [LinearOrder C] [CommRing R]

noncomputable def repeatRows (v : ι → C → R) (L : ℕ) : ι ×ₗ Fin L → C → R :=
  fun p => v (ofLex p).1

theorem remainingPolynomial_eq_deleteTwoProduct (v : ι → C → R) (i j : ι) :
    remainingPolynomial v i j = deleteTwoProduct (fun k => linearForm (v k)) i j := by
  unfold remainingPolynomial formsProduct deleteTwoProduct
  symm
  apply Finset.prod_subtype
  intro k
  simp [and_comm]

theorem formsProduct_repeat (v : ι → C → R) (L : ℕ) :
    formsProduct (repeatRows v L) = (formsProduct v)^L := by
  unfold formsProduct repeatRows
  rw [← ofLex.symm.prod_comp (fun p : ι ×ₗ Fin L => linearForm (v (ofLex p).1))]
  simp only [ofLex_symm_eq, ofLex_toLex, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow]

theorem remainingPolynomial_repeat (v : ι → C → R) {L : ℕ} (hL : 0 < L)
    {i j : ι} (hij : i ≠ j) (a b : Fin L) :
    remainingPolynomial (repeatRows v L) (toLex (i,a)) (toLex (j,b)) =
      (formsProduct v)^(L-1) * remainingPolynomial v i j := by
  rw [remainingPolynomial_eq_deleteTwoProduct]
  change deleteTwoProduct (fun p : ι ×ₗ Fin L => linearForm (v (ofLex p).1)) _ _ = _
  rw [deleteTwoProduct_comp ofLex (fun p : ι × Fin L => linearForm (v p.1))]
  simpa only [ofLex_toLex, formsProduct, remainingPolynomial_eq_deleteTwoProduct] using
    repeat_deleteTwoProduct (fun k => linearForm (v k)) hL hij a b

/-- Full ordered wedge identity under contiguous repetition. It uses no
nonvanishing assumption on the rows or on their linear forms. -/
theorem wedgePolynomial_repeat (v : ι → C → R) {L : ℕ} (hL : 0 < L)
    (a b : C) :
    wedgePolynomial (repeatRows v L) a b =
      MvPolynomial.C ((L : R)^2) * (formsProduct v)^(L-1) *
        wedgePolynomial v a b := by
  classical
  let g : ι → ι → MvPolynomial C R := fun i j =>
    MvPolynomial.C (wedge v i j a b) * remainingPolynomial v i j
  have hg : ∀ i, g i i = 0 := by
    intro i
    simp [g, wedge, mul_comm]
  have ht (x y : ι ×ₗ Fin L) :
      MvPolynomial.C (wedge (repeatRows v L) x y a b) *
          remainingPolynomial (repeatRows v L) x y =
        (formsProduct v)^(L-1) * g (ofLex x).1 (ofLex y).1 := by
    obtain ⟨⟨i,k⟩, rfl⟩ := toLex.surjective x
    obtain ⟨⟨j,l⟩, rfl⟩ := toLex.surjective y
    by_cases hij : i = j
    · subst j
      simp [g, wedge, repeatRows, mul_comm]
    · rw [remainingPolynomial_repeat v hL hij k l]
      simp only [g, wedge, repeatRows, ofLex_toLex]
      ring
  unfold wedgePolynomial
  simp_rw [ht]
  rw [← Finset.mul_sum, repeated_pair_sum g hg L]
  simp only [g, map_pow, map_natCast]
  ring

end Polynomials
end BapatFiniteRank
