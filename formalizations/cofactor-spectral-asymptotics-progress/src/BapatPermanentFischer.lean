import BapatColorTransport
import BapatColorExpansion
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators

/-!
Rank-two permanent/Fischer bridge by finite permutation fibers.
-/

namespace BapatFischer

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators Nat

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

theorem finset_map_eq_iff_colorTransport (s t : Finset ι) (σ : Equiv.Perm ι) :
    s.map σ.toEmbedding = t ↔ ∀ i, i ∈ s ↔ σ i ∈ t := by
  constructor
  · intro h i
    rw [← h]
    simp
  · intro h
    ext i
    simpa using h (σ.symm i)

theorem card_finset_map_fiber (s t : Finset ι) :
    Fintype.card {σ : Equiv.Perm ι // s.map σ.toEmbedding = t} =
      if s.card = t.card then (Nat.factorial s.card) * (Nat.factorial (Fintype.card ι - s.card)) else 0 := by
  classical
  let e : {σ : Equiv.Perm ι // s.map σ.toEmbedding = t} ≃
      ColorTransport (· ∈ s) (· ∈ t) :=
    Equiv.subtypeEquivRight (finset_map_eq_iff_colorTransport s t)
  exact (Fintype.card_congr e).trans (card_colorTransport_finset s t)

section Semiring

variable [CommSemiring R]

/-- Averaging a fixed color choice over all permutations produces its
coefficient sum, with the stabilizer multiplicity k! times (n-k)!. -/
theorem sum_perm_colorWeight (a b : ι → R) (s : Finset ι) :
    (∑ σ : Equiv.Perm ι, colorWeight (a ∘ σ) (b ∘ σ) s) =
      ((Nat.factorial s.card) * (Nat.factorial (Fintype.card ι - s.card)) : ℕ) *
        (twoColorProduct a b).coeff s.card := by
  classical
  calc
    (∑ σ : Equiv.Perm ι, colorWeight (a ∘ σ) (b ∘ σ) s) =
        ∑ σ : Equiv.Perm ι, colorWeight a b (s.map σ.toEmbedding) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact (colorWeight_map a b s σ).symm
    _ = ∑ t : Finset ι, ∑ _σ :
        {σ : Equiv.Perm ι // s.map σ.toEmbedding = t}, colorWeight a b t :=
      (Fintype.sum_fiberwise' (fun σ : Equiv.Perm ι => s.map σ.toEmbedding)
        (colorWeight a b)).symm
    _ = ∑ t : Finset ι,
        (Fintype.card {σ : Equiv.Perm ι // s.map σ.toEmbedding = t} : R) *
          colorWeight a b t := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Nat.factorial s.card) * (Nat.factorial (Fintype.card ι - s.card)) : ℕ) *
        (twoColorProduct a b).coeff s.card := by
      rw [coeff_twoColorProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_finset_map_fiber]
      by_cases h : s.card = t.card
      · simp only [h, ite_true, Nat.cast_mul]
      · simp [h, Ne.symm h]

/-- Regroup the two-color expansion by its actual coefficient degree. -/
theorem sum_colorWeight_by_card (a b : ι → R) (f : ℕ → R) :
    (∑ s : Finset ι, f s.card * colorWeight a b s) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), f k * (twoColorProduct a b).coeff k := by
  classical
  have hmap : ∀ s ∈ (Finset.univ : Finset (Finset ι)),
      s.card ∈ Finset.range (Fintype.card ι + 1) := by
    intro s hs
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le s.card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_twoColorProduct_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_filter.mp hs).2]

/-- The mixed rank-two permanent is the factorial-weighted coefficient
pairing of the two products of linear factors. This proof is purely finite
and valid in every commutative semiring. -/
theorem permanent_twoColor (a b c d : ι → R) :
    Matrix.permanent (fun i j => a i * c j + b i * d j) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((Nat.factorial k) * (Nat.factorial (Fintype.card ι - k)) : ℕ) *
          (twoColorProduct a b).coeff k * (twoColorProduct c d).coeff k := by
  rw [permanent_twoColor_expand, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_perm_colorWeight]
  exact sum_colorWeight_by_card c d
    (fun k => ((Nat.factorial k) * (Nat.factorial (Fintype.card ι - k)) : ℕ) * (twoColorProduct a b).coeff k)

end Semiring

section Complex

/-- Coefficientwise conjugation commutes with selecting a color class. -/
theorem colorWeight_star (a b : ι → ℂ) (s : Finset ι) :
    colorWeight (fun i => star (a i)) (fun i => star (b i)) s =
      star (colorWeight a b s) := by
  simp only [colorWeight, star_mul, star_prod]
  exact mul_comm _ _

theorem coeff_twoColorProduct_star (a b : ι → ℂ) (k : ℕ) :
    (twoColorProduct (fun i => star (a i)) (fun i => star (b i))).coeff k =
      star ((twoColorProduct a b).coeff k) := by
  simp only [coeff_twoColorProduct_filter, star_sum, colorWeight_star]

/-- Fischer squared norm with a separately supplied homogeneous degree.
The degree parameter is not the univariate natDegree, which can drop when
the top coefficient is zero. -/
noncomputable def fischerNormSq (n : ℕ) (p : ℂ[X]) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.factorial (n - k)) * (Nat.factorial k) : ℕ) * Complex.normSq (p.coeff k)

/-- Complex Gram specialization of the mixed permanent identity. -/
theorem permanent_rankTwo_gram (a b : ι → ℂ) :
    Matrix.permanent (fun i j => a i * star (a j) + b i * star (b j)) =
      (fischerNormSq (Fintype.card ι) (twoColorProduct a b) : ℂ) := by
  rw [permanent_twoColor]
  simp only [fischerNormSq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_twoColorProduct_star]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  push_cast
  ring

end Complex

end BapatFischer
