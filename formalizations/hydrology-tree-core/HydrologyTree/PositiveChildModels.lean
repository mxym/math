import HydrologyTree.PositiveSpectrum
import HydrologyTree.PhysicalCancellation
import Mathlib.RingTheory.Coprime.Lemmas

/-! Positive-rate hypotheses and the proved negative-real factorization pass
to every ACTUAL principal child model. No principal spectral input is assumed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma inward_nonroot_pos {n : ℕ} (x : TreeRates n) (ha : ∀ e : Fin n, 0 < x.1 e.succ)
    (v : Fin (n+1)) (hv : v ≠ 0) : 0 < x.1 v := by
  rw [← Fin.succ_pred v hv]
  exact ha _

lemma outward_nonroot_pos {n : ℕ} (x : TreeRates n) (hf : ∀ e : Fin n, 0 < x.2 e)
    (v : Fin (n+1)) (hv : v ≠ 0) : 0 < outwardByVertex x.2 v := by
  rw [← Fin.succ_pred v hv,outwardByVertex_succ]
  exact hf _

/-- The child's root leak is positive because it is the original exit-to-parent rate. -/
theorem positive_child_rates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    0 < (childRates t c x).1 0 ∧
      (∀ e : Fin (childEdgeCount t c), 0 < (childRates t c x).1 e.succ) ∧
      (∀ e : Fin (childEdgeCount t c), 0 < (childRates t c x).2 e) := by
  refine ⟨?_,?_,?_⟩
  · rw [childRates_leak]
    exact inward_nonroot_pos x ha c.val c.property.1
  · intro e
    exact inward_nonroot_pos x ha (childEnumeration t c e.succ).val
      (branchVertex_ne_zero t c (childEnumeration t c e.succ))
  · intro e
    exact outward_nonroot_pos x hf (childEnumeration t c e.succ).val
      (branchVertex_ne_zero t c (childEnumeration t c e.succ))

lemma coprime_linear_of_ne (a b : ℝ) (h : a ≠ b) : IsCoprime (X+C a) (X+C b) := by
  have hn : a-b ≠ 0 := sub_ne_zero.mpr h
  refine ⟨C ((a-b)⁻¹), -C ((a-b)⁻¹), ?_⟩
  calc
    _ = C ((a-b)⁻¹) * C (a-b) := by rw [map_sub]; ring
    _ = 1 := by rw [← map_mul,inv_mul_cancel₀ hn,map_one]

/-- For completely real factorizations, absence of actual common real roots
proves polynomial coprimality; algebraic closure is not silently invoked. -/
theorem linear_factorizations_coprime {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℝ) (q : J → ℝ)
    (h : ∀ z : ℝ, (∏ i : I, (X+C (r i))).eval z = 0 →
      (∏ j : J, (X+C (q j))).eval z ≠ 0) :
    IsCoprime (∏ i : I, (X+C (r i))) (∏ j : J, (X+C (q j))) := by
  classical
  apply IsCoprime.prod_left
  intro i _
  apply IsCoprime.prod_right
  intro j _
  apply coprime_linear_of_ne
  intro hij
  have hp : (∏ k : I, (X+C (r k))).eval (-r i) = 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hq : (∏ k : J, (X+C (q k))).eval (-r i) = 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hij]
  exact h (-r i) hp hq

/-- Actual sibling polynomials are coprime whenever their real principal
spectra are disjoint, for positive physical internal rates. -/
theorem positive_child_characteristics_coprime {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (c d : RootChild t)
    (h : ∀ z : ℝ, (childCharacteristic t x c).eval z = 0 →
      (childCharacteristic t x d).eval z ≠ 0) :
    IsCoprime (childCharacteristic t x c) (childCharacteristic t x d) := by
  have hc := positive_child_rates t x c ha hf
  have hd := positive_child_rates t x d ha hf
  obtain ⟨r,hr,hP⟩ := physical_characteristic_negative_real_factorization
    (childTree t c) (childRates t c x) hc.1 hc.2.1 hc.2.2
  obtain ⟨q,hq,hQ⟩ := physical_characteristic_negative_real_factorization
    (childTree t d) (childRates t d x) hd.1 hd.2.1 hd.2.2
  change IsCoprime (physicalCharacteristic _ _) (physicalCharacteristic _ _)
  rw [hP,hQ]
  apply linear_factorizations_coprime
  intro z hp hq
  apply h z
  · change (physicalCharacteristic _ _).eval z = 0
    rwa [hP]
  · change (physicalCharacteristic _ _).eval z = 0
    rwa [hQ]

end HydrologyTree
