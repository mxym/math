import HydrologyTree.PhysicalStieltjes
import HydrologyTree.EdgeCharacteristic

/-! Exact numerator reconstruction and noncancellation criterion for finite
Stieltjes representations. Coincident rates and zero weights are kept until
noncancellation is proved; they are not silently removed by the definitions. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

def stieltjesDenominator (r : I → ℝ) : ℝ[X] := ∏ i : I, (X+C (r i))
def stieltjesNumerator (r w : I → ℝ) : ℝ[X] :=
  ∑ i : I, C (w i) * ∏ j ∈ Finset.univ.erase i, (X+C (r j))

lemma stieltjesDenominator_monic (r : I → ℝ) : (stieltjesDenominator r).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_add_C (r i))

@[simp] lemma eval_stieltjesDenominator (r : I → ℝ) (s : ℝ) :
    (stieltjesDenominator r).eval s = ∏ i : I, (s+r i) := by
  simp [stieltjesDenominator, Polynomial.eval_prod]

@[simp] lemma eval_stieltjesNumerator (r w : I → ℝ) (s : ℝ) :
    (stieltjesNumerator r w).eval s =
      ∑ i : I, w i * ∏ j ∈ Finset.univ.erase i, (s+r j) := by
  simp [stieltjesNumerator, Polynomial.eval_finsetSum, Polynomial.eval_prod]

lemma stieltjes_sum_mul_denominator (r w : I → ℝ) (s : ℝ) (hs : ∀ i, s+r i ≠ 0) :
    (∑ i : I, w i/(s+r i)) * (stieltjesDenominator r).eval s =
      (stieltjesNumerator r w).eval s := by
  rw [eval_stieltjesDenominator, eval_stieltjesNumerator, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ (fun j : I => s+r j) (Finset.mem_univ i),
    ← mul_assoc, div_mul_cancel₀ _ (hs i)]

/-- Equality of actual rational functions off their poles fixes the complete
unreduced numerator, even when some pole factors later cancel. -/
theorem polynomial_stieltjes_recovery (F : ℝ[X]) (r w : I → ℝ)
    (h : ∀ s : ℝ, (∀ i, s+r i ≠ 0) →
      F.eval s/(stieltjesDenominator r).eval s = ∑ i : I, w i/(s+r i)) :
    F = stieltjesNumerator r w := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinite_nonroots _ (stieltjesDenominator_monic r).ne_zero).mono
  intro s hs
  have hp : (stieltjesDenominator r).eval s ≠ 0 := hs
  have hi : ∀ i, s+r i ≠ 0 := by
    rw [eval_stieltjesDenominator, Finset.prod_ne_zero_iff] at hp
    exact fun i => hp i (Finset.mem_univ i)
  have he := congrArg (fun z : ℝ => z*(stieltjesDenominator r).eval s) (h s hi)
  rw [div_mul_cancel₀ _ hp, stieltjes_sum_mul_denominator r w s hi] at he
  exact he

@[simp] lemma stieltjesDenominator_eval_pole (r : I → ℝ) (i : I) :
    (stieltjesDenominator r).eval (-r i) = 0 := by
  rw [eval_stieltjesDenominator]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)

/-- Exact numerator value at a pole; valid even when other rates coincide. -/
theorem stieltjesNumerator_eval_pole (r w : I → ℝ) (i : I) :
    (stieltjesNumerator r w).eval (-r i) =
      w i * ∏ j ∈ Finset.univ.erase i, (r j-r i) := by
  rw [eval_stieltjesNumerator, Finset.sum_eq_single i]
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    ring
  · intro j _ hji
    have hi : i ∈ Finset.univ.erase j := by simp [Ne.symm hji]
    have hz : (∏ k ∈ Finset.univ.erase j, (-r i+r k)) = 0 :=
      Finset.prod_eq_zero hi (by ring)
    rw [hz, mul_zero]
  · simp

/-- Absence of cancellation forces distinct poles and nonzero observation weights. -/
theorem stieltjes_noncancellation_forces_modes (r w : I → ℝ)
    (h : ∀ z : ℝ, (stieltjesDenominator r).eval z = 0 →
      (stieltjesNumerator r w).eval z ≠ 0) :
    Function.Injective r ∧ ∀ i, w i ≠ 0 := by
  have hm (i : I) : w i * (∏ j ∈ Finset.univ.erase i, (r j-r i)) ≠ 0 := by
    simpa only [stieltjesNumerator_eval_pole] using h (-r i) (stieltjesDenominator_eval_pole r i)
  constructor
  · intro i j hij
    by_contra hne
    have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm hne]
    have hz : (∏ k ∈ Finset.univ.erase i, (r k-r i)) = 0 :=
      Finset.prod_eq_zero hj (sub_eq_zero.mpr hij.symm)
    exact hm i (by rw [hz, mul_zero])
  · intro i
    exact left_ne_zero_of_mul (hm i)

/-- Distinct poles with nonzero observation weights also rule out every common
root; with nonnegative weights this is equivalent to every weight being positive. -/
theorem stieltjes_modes_force_noncancellation (r w : I → ℝ)
    (hr : Function.Injective r) (hw : ∀ i, w i ≠ 0) :
    ∀ z : ℝ, (stieltjesDenominator r).eval z = 0 →
      (stieltjesNumerator r w).eval z ≠ 0 := by
  intro z hz
  rw [eval_stieltjesDenominator, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i,_,hi⟩ := hz
  have he : z = -r i := by linarith
  rw [he, stieltjesNumerator_eval_pole]
  apply mul_ne_zero (hw i)
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hji
  exact (Finset.mem_erase.mp hj).1 (hr hji)

/-- The actual unreduced cofactor has the complete positive-tree spectral
numerator formula, not just a fitted response or selected pole values. -/
theorem physical_stieltjes_polynomials {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    ∃ r w : Fin (n+1) → ℝ, (∀ i, 0 < r i) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i)=1 ∧
      physicalCharacteristic t x = stieltjesDenominator r ∧
      physicalRootCofactor t x = stieltjesNumerator r w := by
  obtain ⟨r,w,hr,hw,hm,hP,hR⟩ := physical_finite_stieltjes t x hell ha hf
  refine ⟨r,w,hr,hw,hm,hP,?_⟩
  apply polynomial_stieltjes_recovery
  intro s hs
  have h := hR s hs
  rw [physicalRootResponse_eq, hP] at h
  exact h

end HydrologyTree
