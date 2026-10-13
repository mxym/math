import HydrologyTree.SpectralFactorMatching

/-! Equal complete Stieltjes polynomial pairs determine every weighted spectral
sum. This transfers dynamical formulas without choosing unproved mode labels. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma stieltjes_weights_unique {I : Type*} [Fintype I] [DecidableEq I]
    (r w v : I → ℝ) (hr : Function.Injective r)
    (h : stieltjesNumerator r w=stieltjesNumerator r v) : w=v := by
  funext i
  have he := congrArg (fun P : ℝ[X] => P.eval (-r i)) h
  rw [stieltjesNumerator_eval_pole,stieltjesNumerator_eval_pole] at he
  have hn : (∏ j ∈ Finset.univ.erase i, (r j-r i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun hji => (Finset.mem_erase.mp hj).1 (hr hji))
  exact mul_right_cancel₀ hn he

/-- Exact matching of weights as well as poles. -/
theorem stieltjes_pair_matching {n : ℕ} (q r w v : Fin (n+1) → ℝ)
    (hr : Function.Injective r)
    (hP : stieltjesDenominator q=stieltjesDenominator r)
    (hF : stieltjesNumerator q w=stieltjesNumerator r v) :
    ∃ e : Fin (n+1) ≃ Fin (n+1), (∀ i, q i=r (e i)) ∧ ∀ i, w i=v (e i) := by
  obtain ⟨e,he⟩ := stieltjes_factor_matching (Equiv.refl _) q r hr hP
  have hq : Function.Injective q := by
    intro i j hij
    apply e.injective
    apply hr
    rwa [← he i,← he j]
  have hN : stieltjesNumerator q w=stieltjesNumerator q (fun i => v (e i)) := by
    calc
      _ = stieltjesNumerator r v := hF
      _ = stieltjesNumerator (fun i => r (e i)) (fun i => v (e i)) :=
        (stieltjesNumerator_reindex e r v).symm
      _ = _ := by rw [← funext he]
  have hw := stieltjes_weights_unique q w (fun i => v (e i)) hq hN
  exact ⟨e,he,fun i => congrFun hw i⟩

/-- Arbitrary spectral test functions, including actual time-domain responses. -/
theorem stieltjes_weighted_sum_congr {n : ℕ} (q r w v : Fin (n+1) → ℝ)
    (hr : Function.Injective r)
    (hP : stieltjesDenominator q=stieltjesDenominator r)
    (hF : stieltjesNumerator q w=stieltjesNumerator r v) (f : ℝ → ℝ) :
    (∑ i, w i*f (q i))=∑ i, v i*f (r i) := by
  obtain ⟨e,he,hw⟩ := stieltjes_pair_matching q r w v hr hP hF
  calc
    _ = ∑ i, v (e i)*f (r (e i)) := by simp only [he,hw]
    _ = _ := e.sum_comp (fun i => v i*f (r i))

end HydrologyTree
