import HydrologyTree.ReciprocalInterpolation

/-! Complete constructive reciprocal Stieltjes transformation. Every zero,
residue, polynomial identity and root leak positivity is proved from the
specified positive normalized response, with the one-store case included. -/
open Polynomial
noncomputable section
namespace HydrologyTree

def reciprocalDiagonal {n : ℕ} (r w : Fin (n+1) → ℝ) : ℝ :=
  ((stieltjesDenominator r /ₘ stieltjesNumerator r w).coeff 0)

/-- Complete polynomial identity for the positive reciprocal transformation. -/
theorem stieltjes_reciprocal_polynomial {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    stieltjesDenominator r = (X+C (reciprocalDiagonal r w))*stieltjesNumerator r w -
      stieltjesNumerator (stieltjesZeroRates r w hr hw) (reciprocalResidue r w hr hw) := by
  have h := polynomial_reciprocal_interpolation (stieltjesDenominator r)
    (stieltjesZeroRates r w hr hw) (reciprocalResidue r w hr hw)
    (stieltjesDenominator_monic r) (stieltjesDenominator_natDegree r)
    (stieltjesZeroRates_strictMono r w hr hw).injective
    (fun i => by rw [← stieltjesNumerator_interlacing_factorization r w hr hw hm]; rfl)
  rw [← stieltjesNumerator_interlacing_factorization r w hr hw hm] at h
  exact h

lemma stieltjesDenominator_eval_zero_pos {I : Type*} [Fintype I]
    (r : I → ℝ) (hr : ∀ i, 0 < r i) : 0 < (stieltjesDenominator r).eval 0 := by
  classical
  rw [eval_stieltjesDenominator]
  apply Finset.prod_pos
  intro i _
  simpa using hr i

/-- The root-leak value required by conservative reconstruction is strictly
positive. It is computed from the original reciprocal response at zero. -/
theorem reciprocal_leak_formula {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hpos : ∀ i, 0 < r i) :
    reciprocalDiagonal r w - ∑ i : Fin n,
        reciprocalResidue r w hr hw i/stieltjesZeroRates r w hr hw i =
      (stieltjesDenominator r).eval 0/(stieltjesNumerator r w).eval 0 ∧
    0 < reciprocalDiagonal r w - ∑ i : Fin n,
        reciprocalResidue r w hr hw i/stieltjesZeroRates r w hr hw i := by
  let b := stieltjesZeroRates r w hr hw
  let g := reciprocalResidue r w hr hw
  have hF : stieltjesNumerator r w = stieltjesDenominator b :=
    stieltjesNumerator_interlacing_factorization r w hr hw hm
  have hb : ∀ i, 0 < b i := stieltjesZeroRates_pos r w hr hw hpos
  have hFpos : 0 < (stieltjesNumerator r w).eval 0 := by
    rw [hF]
    exact stieltjesDenominator_eval_zero_pos b hb
  have hDpos := stieltjesDenominator_eval_zero_pos r hpos
  have hq := stieltjes_quotient_eq_sum b g 0 (fun i => by simpa using ne_of_gt (hb i))
  have h := congrArg (fun P : ℝ[X] => P.eval 0) (stieltjes_reciprocal_polynomial r w hr hw hm)
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C,zero_add] at h
  have he : reciprocalDiagonal r w-∑ i : Fin n, g i/b i =
      (stieltjesDenominator r).eval 0/(stieltjesNumerator r w).eval 0 := by
    rw [← hF] at hq
    simp only [zero_add] at hq
    rw [← hq]
    apply (eq_div_iff (ne_of_gt hFpos)).mpr
    rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hFpos)]
    exact h.symm
  refine ⟨he,?_⟩
  rw [he]
  exact div_pos hDpos hFpos

/-- Complete existence theorem for the reciprocal data, all finite sizes.
No abstract interlacing theorem, residue positivity, or realization assumption
is used as an input. -/
theorem exists_positive_reciprocal_stieltjes_data {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i)
    (hm : (∑ i, w i)=1) :
    ∃ (b g : Fin n → ℝ) (d : ℝ),
      StrictMono b ∧ (∀ i, r i.castSucc < b i ∧ b i < r i.succ) ∧
      (∀ i, 0 < b i) ∧ (∀ i, 0 < g i) ∧
      stieltjesNumerator r w = stieltjesDenominator b ∧
      stieltjesDenominator r = (X+C d)*stieltjesDenominator b-stieltjesNumerator b g ∧
      0 < d-∑ i, g i/b i := by
  refine ⟨stieltjesZeroRates r w hr hw,reciprocalResidue r w hr hw,reciprocalDiagonal r w,
    stieltjesZeroRates_strictMono r w hr hw,?_,stieltjesZeroRates_pos r w hr hw hpos,
    reciprocalResidue_pos r w hr hw,stieltjesNumerator_interlacing_factorization r w hr hw hm,?_,
    (reciprocal_leak_formula r w hr hw hm hpos).2⟩
  · intro i
    exact ⟨(stieltjesZeroRates_spec r w hr hw i).1,(stieltjesZeroRates_spec r w hr hw i).2.1⟩
  · rw [← stieltjesNumerator_interlacing_factorization r w hr hw hm]
    exact stieltjes_reciprocal_polynomial r w hr hw hm

end HydrologyTree
