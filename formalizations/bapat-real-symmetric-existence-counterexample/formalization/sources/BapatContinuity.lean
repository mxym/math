import BapatDefs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real

open scoped BigOperators ComplexOrder Topology
open Filter Set Polynomial

set_option autoImplicit false

namespace BapatRankTwo

/-- Endpoint negativity already precludes monotonicity on the original interval. -/
theorem not_monotoneOn_of_derivative_one_neg (P : ℝ[X])
    (hP : P.derivative.eval 1 < 0) :
    ¬ MonotoneOn (fun q : ℝ => P.eval q) (Icc (-1) 1) := by
  intro hm
  have hu : UniqueDiffWithinAt ℝ (Icc (-1 : ℝ) 1) 1 :=
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) 1 (by norm_num)
  have he := (P.hasDerivAt 1).hasDerivWithinAt.derivWithin hu
  have hn := hm.derivWithin_nonneg (x := 1)
  rw [he] at hn
  exact (not_le_of_gt hP) hn

/-- The decrease can be witnessed strictly inside the interval. -/
theorem exists_interior_decrease_of_derivative_one_neg (P : ℝ[X])
    (hP : P.derivative.eval 1 < 0) :
    ∃ a ∈ Ioo (-1 : ℝ) 1, ∃ b ∈ Ioo (-1 : ℝ) 1,
      a < b ∧ P.eval b < P.eval a := by
  have hn : ∀ᶠ x : ℝ in 𝓝 1, P.derivative.eval x < 0 :=
    P.derivative.continuousAt.eventually (gt_mem_nhds hP)
  have hl : ∀ᶠ x : ℝ in 𝓝 1, (-1 : ℝ) < x := lt_mem_nhds (by norm_num)
  have hboth : ∀ᶠ x : ℝ in 𝓝[<] 1, P.derivative.eval x < 0 ∧ -1 < x :=
    (hn.and hl).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, ⟨hxneg, hxlo⟩, hxhi⟩ := (hboth.and self_mem_nhdsWithin).exists
  have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨hxlo, hxhi⟩
  have hmono : ¬ MonotoneOn (fun q : ℝ => P.eval q) (Ioo (-1) 1) := by
    intro hm
    have hu := isOpen_Ioo.uniqueDiffOn (𝕜 := ℝ) x hx
    have he := (P.hasDerivAt x).hasDerivWithinAt.derivWithin hu
    have hz := hm.derivWithin_nonneg (x := x)
    rw [he] at hz
    exact (not_le_of_gt hxneg) hz
  unfold MonotoneOn at hmono
  push Not at hmono
  obtain ⟨a, ha, b, hb, hab, hd⟩ := hmono
  refine ⟨a, ha, b, hb, lt_of_le_of_ne hab ?_, hd⟩
  intro he
  subst b
  exact lt_irrefl _ hd

/-- The endpoint derivative varies continuously under a real diagonal perturbation. -/
theorem continuous_perturb_derivative_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun δ : ℝ => (realQPolynomial (perturb A δ)).derivative.eval 1) := by
  simp_rw [realQPolynomial_derivative_one]
  unfold MarkedInversions.weightedInversionSum MarkedInversions.permutationWeight
  unfold perturb Matrix.diagonal
  continuity

/-- A strict negative derivative at a PSD matrix survives a small positive
diagonal perturbation, producing a genuine complex Hermitian PD counterexample. -/
theorem bapatConjecture_false_of_psd_derivative_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hneg : (realQPolynomial A).derivative.eval 1 < 0) :
    ¬ BapatConjecture := by
  have hcont := (continuous_perturb_derivative_one A).continuousAt (x := 0)
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0,
      (realQPolynomial (perturb A δ)).derivative.eval 1 < 0 :=
    hcont.eventually (gt_mem_nhds (by simpa using hneg))
  have hright : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (realQPolynomial (perturb A δ)).derivative.eval 1 < 0 :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδneg, hδ⟩ := (hright.and self_mem_nhdsWithin).exists
  intro hconj
  have hm := hconj n (perturb A δ) (perturb_posDef hA hδ)
  have hm' : MonotoneOn (fun q : ℝ => (realQPolynomial (perturb A δ)).eval q)
      (Icc (-1) 1) := by
    simpa only [realQPolynomial_eval] using hm
  exact not_monotoneOn_of_derivative_one_neg _ hδneg hm'

/-- Explicit existential scope: same dimension, positive diagonal shift,
strict positive definiteness, and two ordered points strictly in (-1,1). -/
theorem exists_posDef_interior_counterexample_of_psd_derivative_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hneg : (realQPolynomial A).derivative.eval 1 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ (perturb A δ).PosDef ∧
      ∃ a ∈ Ioo (-1 : ℝ) 1, ∃ b ∈ Ioo (-1 : ℝ) 1,
        a < b ∧ (qPermanent (perturb A δ) (b : ℂ)).re <
          (qPermanent (perturb A δ) (a : ℂ)).re := by
  have hcont := (continuous_perturb_derivative_one A).continuousAt (x := 0)
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0,
      (realQPolynomial (perturb A δ)).derivative.eval 1 < 0 :=
    hcont.eventually (gt_mem_nhds (by simpa using hneg))
  have hright : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (realQPolynomial (perturb A δ)).derivative.eval 1 < 0 :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδneg, hδ⟩ := (hright.and self_mem_nhdsWithin).exists
  obtain ⟨a, ha, b, hb, hab, hd⟩ :=
    exists_interior_decrease_of_derivative_one_neg _ hδneg
  exact ⟨δ, hδ, perturb_posDef hA hδ, a, ha, b, hb, hab,
    by simpa only [realQPolynomial_eval] using hd⟩

end BapatRankTwo
