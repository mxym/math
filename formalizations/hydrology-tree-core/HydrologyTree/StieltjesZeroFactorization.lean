import HydrologyTree.StieltjesInterlacing

/-! Complete numerator factorization by the interlacing zeros constructed from
positive weights. This establishes every zero and its simplicity, not merely
existence of a selection of roots. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma stieltjesDenominator_degree_card {I : Type*} [Fintype I] (r : I → ℝ) :
    (stieltjesDenominator r).natDegree = Fintype.card I := by
  classical
  rw [stieltjesDenominator,Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_add_C (r i))]
  simp

lemma stieltjes_numerator_interlacing_divides {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) :
    stieltjesDenominator (stieltjesZeroRates r w hr hw) ∣ stieltjesNumerator r w := by
  unfold stieltjesDenominator
  apply Fintype.prod_dvd_of_coprime
  · have hmono := stieltjesZeroRates_strictMono r w hr hw
    have hinj : Function.Injective (fun i => -stieltjesZeroRates r w hr hw i) :=
      neg_injective.comp hmono.injective
    simpa only [Function.comp_def,Function.onFun,map_neg,sub_neg_eq_add] using
      Polynomial.pairwise_coprime_X_sub_C hinj
  · intro i
    have h := Polynomial.dvd_iff_isRoot.mpr (stieltjesZeroRates_spec r w hr hw i).2.2
    simpa only [map_neg,sub_neg_eq_add] using h

/-- Complete monic numerator factorization at the constructed interlacing roots.
The normalization is explicit and n=0 is included. -/
theorem stieltjesNumerator_interlacing_factorization {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    stieltjesNumerator r w = stieltjesDenominator (stieltjesZeroRates r w hr hw) := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (stieltjesDenominator_monic _) (normalized_stieltjesNumerator_monic r w hm)
    (stieltjes_numerator_interlacing_divides r w hr hw)
  rw [normalized_stieltjesNumerator_degree r w hm,stieltjesDenominator_degree_card]
  simp

/-- No additional real numerator zeros exist outside the constructed family. -/
theorem stieltjesNumerator_zero_iff {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (b : ℝ) :
    (stieltjesNumerator r w).eval (-b)=0 ↔ ∃ i : Fin n, b=stieltjesZeroRates r w hr hw i := by
  rw [stieltjesNumerator_interlacing_factorization r w hr hw hm,eval_stieltjesDenominator,
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,by linarith⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,by rw [hi]; ring⟩

lemma stieltjesDenominator_derivative {I : Type*} [Fintype I] [DecidableEq I] (r : I → ℝ) :
    (stieltjesDenominator r).derivative = stieltjesNumerator r (fun _ => 1) := by
  rw [stieltjesDenominator,Polynomial.derivative_prod_finset]
  simp [stieltjesNumerator]

/-- Each interlacing zero is simple: the derivative value is an explicit
nonzero product of distinct zero-rate differences. -/
theorem stieltjesNumerator_derivative_at_zero {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (i : Fin n) :
    (stieltjesNumerator r w).derivative.eval (-stieltjesZeroRates r w hr hw i) =
      ∏ j ∈ Finset.univ.erase i,
        (stieltjesZeroRates r w hr hw j-stieltjesZeroRates r w hr hw i) := by
  rw [stieltjesNumerator_interlacing_factorization r w hr hw hm,
    stieltjesDenominator_derivative,stieltjesNumerator_eval_pole,one_mul]

theorem stieltjesNumerator_simple_zeros {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (i : Fin n) :
    (stieltjesNumerator r w).derivative.eval (-stieltjesZeroRates r w hr hw i) ≠ 0 := by
  rw [stieltjesNumerator_derivative_at_zero r w hr hw hm]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  intro he
  exact (Finset.mem_erase.mp hj).1
    ((stieltjesZeroRates_strictMono r w hr hw).injective (sub_eq_zero.mp he))

end HydrologyTree
