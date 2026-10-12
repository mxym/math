import BapatRationalPerturbation
import BapatContinuity
import Mathlib.LinearAlgebra.Matrix.IsDiag

set_option autoImplicit false
open MeasureTheory Filter Set BapatFiniteRank BapatRankTwo.MarkedInversions
open scoped Topology

namespace BapatRealExistence
noncomputable section

theorem exists_positive_interior_decrease (P : Polynomial ℝ) (hP : P.derivative.eval 1<0) :
    ∃ a ∈ Ioo (0:ℝ) 1, ∃ b ∈ Ioo (0:ℝ) 1, a<b ∧ P.eval b<P.eval a := by
  have hn : ∀ᶠ x : ℝ in 𝓝 1, P.derivative.eval x<0 :=
    P.derivative.continuousAt.eventually (gt_mem_nhds hP)
  have hl : ∀ᶠ x : ℝ in 𝓝 1, (0:ℝ)<x := lt_mem_nhds (by norm_num)
  have hboth : ∀ᶠ x : ℝ in 𝓝[<] 1, P.derivative.eval x<0 ∧ 0<x :=
    (hn.and hl).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,⟨hxneg,hxlo⟩,hxhi⟩ := (hboth.and self_mem_nhdsWithin).exists
  have hx : x∈Ioo (0:ℝ) 1 := ⟨hxlo,hxhi⟩
  have hmono : ¬ MonotoneOn P.eval (Ioo (0:ℝ) 1) := by
    intro hm
    have hu := isOpen_Ioo.uniqueDiffOn (𝕜 := ℝ) x hx
    have he := (P.hasDerivAt x).hasDerivWithinAt.derivWithin hu
    have hz := hm.derivWithin_nonneg (x := x)
    rw [he] at hz
    exact (not_le_of_gt hxneg) hz
  unfold MonotoneOn at hmono
  push Not at hmono
  obtain ⟨a,ha,b,hb,hab,hd⟩ := hmono
  refine ⟨a,ha,b,hb,lt_of_le_of_ne hab ?_,hd⟩
  intro he
  subst b
  exact lt_irrefl _ hd

theorem exists_rational_interior_decrease (P : Polynomial ℝ) (hP : P.derivative.eval 1<0) :
    ∃ q₀ q₁ : ℚ, 0<q₀ ∧ q₀<q₁ ∧ q₁<1 ∧ P.eval (q₁:ℝ)<P.eval (q₀:ℝ) := by
  obtain ⟨a,ha,b,hb,hab,hd⟩ := exists_positive_interior_decrease P hP
  have hdense : DenseRange (fun q : ℚ × ℚ => ((q.1:ℝ),(q.2:ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have ho : IsOpen {p : ℝ × ℝ | 0<p.1 ∧ p.1<p.2 ∧ p.2<1 ∧ P.eval p.2<P.eval p.1} := by
    apply IsOpen.inter (isOpen_lt continuous_const continuous_fst)
    apply IsOpen.inter (isOpen_lt continuous_fst continuous_snd)
    apply IsOpen.inter (isOpen_lt continuous_snd continuous_const)
    exact isOpen_lt (P.continuous.comp continuous_snd) (P.continuous.comp continuous_fst)
  obtain ⟨q,hq₀,hqq,hq₁,hqdec⟩ := hdense.exists_mem_open ho ⟨(a,b),ha.1,hab,hb.2,hd⟩
  dsimp only at hq₀ hqq hq₁ hqdec
  exact ⟨q.1,q.2,by exact_mod_cast hq₀,by exact_mod_cast hqq,by exact_mod_cast hq₁,hqdec⟩

theorem derivative_one_eq_zero_of_isDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsDiag) : (qPolynomial A).derivative.eval 1=0 := by
  classical
  rw [qPolynomial_derivative_one]
  unfold weightedInversionSum
  apply Finset.sum_eq_zero
  intro σ hσ
  by_cases hs : σ=1
  · subst σ
    have hinv : originalInversions (1 : Equiv.Perm (Fin n))=0 := by
      unfold originalInversions
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp
      simp only [Equiv.Perm.one_apply]
      exact fun h => lt_asymm h.1 h.2
    rw [hinv,Nat.cast_zero,zero_mul]
  · have hi : ∃ i, σ i≠i := by
      by_contra h
      apply hs
      apply Equiv.ext
      intro i
      simpa using not_exists.mp h i
    obtain ⟨i,hi⟩ := hi
    have hw : permutationWeight A σ=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hA hi.symm
    rw [hw,mul_zero]

theorem not_isDiag_of_negative_endpoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : (qPolynomial A).derivative.eval 1<0) : ¬ A.IsDiag := by
  intro hd
  rw [derivative_one_eq_zero_of_isDiag A hd] at hA
  exact lt_irrefl _ hA

end
end BapatRealExistence
