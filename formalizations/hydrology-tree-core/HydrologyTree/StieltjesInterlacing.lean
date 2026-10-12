import HydrologyTree.StieltjesDegree
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-! Actual real zeros between every pair of consecutive Stieltjes poles.
Existence follows from a proved polynomial sign calculation and the IVT;
it is not supplied by a spectral oracle or a root-finding computation. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma fin_stieltjes_adjacent_lt {n : ℕ} (i : Fin n) : i.castSucc < i.succ := by
  change i.val < i.val+1
  omega

lemma fin_stieltjes_outside_adjacent {n : ℕ} (i : Fin n) (j : Fin (n+1))
    (hlo : j ≠ i.castSucc) (hhi : j ≠ i.succ) : j < i.castSucc ∨ i.succ < j := by
  have hl : j.val ≠ i.val := fun h => hlo (Fin.ext h)
  have hh : j.val ≠ i.val+1 := fun h => hhi (Fin.ext h)
  change j.val < i.val ∨ i.val+1 < j.val
  omega

lemma adjacentPole_other_product_pos {n : ℕ} (r : Fin (n+1) → ℝ) (hr : StrictMono r)
    (i : Fin n) :
    0 < ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ,
      (r j-r i.castSucc)*(r j-r i.succ) := by
  apply Finset.prod_pos
  intro j hj
  have hji : j ≠ i.castSucc := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hjs : j ≠ i.succ := (Finset.mem_erase.mp hj).1
  rcases fin_stieltjes_outside_adjacent i j hji hjs with hlt | hgt
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hr hlt))
      (sub_neg.mpr (hr (lt_trans hlt (fin_stieltjes_adjacent_lt i))))
  · exact mul_pos (sub_pos.mpr (hr (lt_trans (fin_stieltjes_adjacent_lt i) hgt)))
      (sub_pos.mpr (hr hgt))

/-- Consecutive pole evaluations of the ACTUAL numerator have opposite signs. -/
theorem stieltjesNumerator_adjacent_poles_opposite {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) (i : Fin n) :
    (stieltjesNumerator r w).eval (-r i.castSucc) *
      (stieltjesNumerator r w).eval (-r i.succ) < 0 := by
  have hneq : i.castSucc ≠ i.succ := ne_of_lt (fin_stieltjes_adjacent_lt i)
  have hs : i.succ ∈ (Finset.univ : Finset (Fin (n+1))).erase i.castSucc := by simp [Ne.symm hneq]
  have hl : i.castSucc ∈ (Finset.univ : Finset (Fin (n+1))).erase i.succ := by simp [hneq]
  have hgap : 0 < r i.succ-r i.castSucc := sub_pos.mpr (hr (fin_stieltjes_adjacent_lt i))
  have hrest := adjacentPole_other_product_pos r hr i
  have herase : ((Finset.univ : Finset (Fin (n+1))).erase i.succ).erase i.castSucc =
      (Finset.univ.erase i.castSucc).erase i.succ := by
    ext j
    simp only [Finset.mem_erase]
    tauto
  have hid : (stieltjesNumerator r w).eval (-r i.castSucc) *
      (stieltjesNumerator r w).eval (-r i.succ) =
      -((w i.castSucc*w i.succ)*(r i.succ-r i.castSucc)^2 *
        ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ,
          (r j-r i.castSucc)*(r j-r i.succ)) := by
    rw [stieltjesNumerator_eval_pole,stieltjesNumerator_eval_pole,
      ← Finset.mul_prod_erase (Finset.univ.erase i.castSucc) (fun j => r j-r i.castSucc) hs,
      ← Finset.mul_prod_erase (Finset.univ.erase i.succ) (fun j => r j-r i.succ) hl,
      herase,Finset.prod_mul_distrib]
    ring
  rw [hid]
  exact neg_lt_zero.mpr (mul_pos (mul_pos (mul_pos (hw _) (hw _)) (sq_pos_of_pos hgap)) hrest)

lemma polynomial_zero_between_opposite (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (h : p.eval a*p.eval b < 0) : ∃ z : ℝ, a < z ∧ z < b ∧ p.eval z = 0 := by
  have hu : (0 : ℝ) ∈ Set.uIcc (p.eval a) (p.eval b) := by
    rw [Set.mem_uIcc]
    rcases mul_neg_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    all_goals first | exact Or.inl ⟨ha.le,hb.le⟩ | exact Or.inr ⟨hb.le,ha.le⟩
  obtain ⟨z,hz,hzero⟩ := intermediate_value_uIcc (p.continuous.continuousOn) hu
  change p.eval z = 0 at hzero
  have hz' : a ≤ z ∧ z ≤ b := by simpa only [Set.uIcc_of_le hab.le,Set.mem_Icc] using hz
  have hza : z ≠ a := by intro he; rw [he] at hzero; rw [hzero,zero_mul] at h; exact (lt_irrefl _ h)
  have hzb : z ≠ b := by intro he; rw [he] at hzero; rw [hzero,mul_zero] at h; exact (lt_irrefl _ h)
  exact ⟨z,lt_of_le_of_ne hz'.1 (Ne.symm hza),lt_of_le_of_ne hz'.2 hzb,hzero⟩

/-- An actual numerator zero strictly between each consecutive pair of poles. -/
theorem stieltjes_interlacing_zero_exists {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) (i : Fin n) :
    ∃ b : ℝ, r i.castSucc < b ∧ b < r i.succ ∧ (stieltjesNumerator r w).eval (-b)=0 := by
  have hg : r i.castSucc < r i.succ := hr (fin_stieltjes_adjacent_lt i)
  have hs := stieltjesNumerator_adjacent_poles_opposite r w hr hw i
  rw [mul_comm] at hs
  obtain ⟨z,hz1,hz2,hzero⟩ := polynomial_zero_between_opposite
    (stieltjesNumerator r w) (-r i.succ) (-r i.castSucc) (neg_lt_neg hg) hs
  refine ⟨-z,?_,?_,?_⟩
  · linarith
  · linarith
  · simpa only [neg_neg] using hzero

/-- Choose all zeros together; uniqueness and full factorization are established separately. -/
def stieltjesZeroRates {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) : Fin n → ℝ :=
  fun i => Classical.choose (stieltjes_interlacing_zero_exists r w hr hw i)

lemma stieltjesZeroRates_spec {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) (i : Fin n) :
    r i.castSucc < stieltjesZeroRates r w hr hw i ∧
      stieltjesZeroRates r w hr hw i < r i.succ ∧
      (stieltjesNumerator r w).eval (-stieltjesZeroRates r w hr hw i)=0 :=
  Classical.choose_spec (stieltjes_interlacing_zero_exists r w hr hw i)

theorem stieltjesZeroRates_strictMono {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) : StrictMono (stieltjesZeroRates r w hr hw) := by
  intro i j hij
  have h1 := (stieltjesZeroRates_spec r w hr hw i).2.1
  have h2 := (stieltjesZeroRates_spec r w hr hw j).1
  have hmid : r i.succ ≤ r j.castSucc := hr.monotone (by
    change i.val+1 ≤ j.val
    exact Nat.succ_le_of_lt (show i.val < j.val from hij))
  exact lt_trans (lt_of_lt_of_le h1 hmid) h2

lemma stieltjesZeroRates_pos {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : StrictMono r) (hw : ∀ j, 0 < w j) (hpos : ∀ j, 0 < r j) (i : Fin n) :
    0 < stieltjesZeroRates r w hr hw i :=
  lt_trans (hpos i.castSucc) (stieltjesZeroRates_spec r w hr hw i).1

end HydrologyTree
