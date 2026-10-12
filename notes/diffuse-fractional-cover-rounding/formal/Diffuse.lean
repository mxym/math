import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DiffuseFractionalCover

theorem three_complement_intersection (a b : Fin 3) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  have h : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
  exact h a b

theorem three_complement_incidence_count (a : Fin 3) :
    (Finset.univ.filter (fun c : Fin 3 => c ≠ a)).card = 2 := by
  have h : ∀ a : Fin 3, (Finset.univ.filter (fun c : Fin 3 => c ≠ a)).card = 2 := by decide
  exact h a

theorem repair_margin (D m r L gap : ℝ)
    (hD : 3 ≤ D) (hgap : gap = (D-1)*m-D*(D-2)*r-D)
    (hstrict : D*(D-2)*L < gap) :
    ((D-2)*(r+L)+1)/(D-1) < m/D := by
  have hp : 0 < D := by linarith
  have hq : 0 < D-1 := by linarith
  apply (div_lt_div_iff₀ hq hp).mpr
  nlinarith only [hgap,hstrict]

theorem peak_removal_margin (K gap M L : ℝ)
    (hK : 0 < K) (hg : 0 < gap) (hM : K/gap < M)
    (hL : L ≤ 1/M) : K*L < gap := by
  have hMpos : 0 < M := lt_trans (div_pos hK hg) hM
  have hmul : K < M*gap := (div_lt_iff₀ hg).mp hM
  have hbound : L*M ≤ 1 := (le_div_iff₀ hMpos).mp hL
  have hprod : K*(L*M) ≤ K := by
    have ht := mul_le_mul_of_nonneg_left hbound (le_of_lt hK)
    simpa using ht
  have hres : K*L*M < gap*M := by nlinarith only [hprod,hmul]
  by_contra hnot
  have hn : 0 ≤ K*L-gap := by linarith
  have hprod' := mul_nonneg hn (le_of_lt hMpos)
  nlinarith only [hres,hprod']

def pairCount {ι V : Type*} [DecidableEq V] (B : Finset ι)
    (A : ι → Finset V) (p q : V) : ℝ :=
  ∑ e ∈ B, if p ∈ A e ∧ q ∈ A e then (1 : ℝ) else 0

def restrictionLoad {ι V : Type*} [DecidableEq V] (B : Finset ι)
    (A : ι → Finset V) (t : ι → ℝ) (S : Finset V) (p : V) : ℝ :=
  ∑ e ∈ B, if p ∈ A e ∧ ((S.erase p).filter (fun q => q ∈ A e)).Nonempty
    then t e else 0

theorem actual_restriction_budget {ι V : Type*} [DecidableEq V]
    (B : Finset ι) (A : ι → Finset V) (t : ι → ℝ) (S : Finset V) (p : V)
    (M budget : ℝ) (hM : 0 ≤ M) (hcap : ∀ e ∈ B, t e ≤ M)
    (hbudget : (∑ q ∈ S.erase p, pairCount B A p q) ≤ budget) :
    restrictionLoad B A t S p ≤ M*budget := by
  let count : ι → ℝ := fun e => ∑ q ∈ S.erase p, if q ∈ A e then (1 : ℝ) else 0
  have hcpos : ∀ e, 0 ≤ count e := by
    intro e
    apply Finset.sum_nonneg
    intro q hq
    split <;> norm_num
  have hterm : ∀ e ∈ B,
      (if p ∈ A e ∧ ((S.erase p).filter (fun q => q ∈ A e)).Nonempty then t e else 0)
        ≤ M*(if p ∈ A e then count e else 0) := by
    intro e he
    by_cases hp : p ∈ A e
    · by_cases hn : ((S.erase p).filter (fun q => q ∈ A e)).Nonempty
      · have htrue : p ∈ A e ∧ ((S.erase p).filter (fun q => q ∈ A e)).Nonempty := ⟨hp,hn⟩
        obtain ⟨q,hq⟩ := hn
        obtain ⟨hqS,hqA⟩ := Finset.mem_filter.mp hq
        have hsingle : 1 ≤ count e := by
          have hs := Finset.single_le_sum
            (f := fun q => if q ∈ A e then (1 : ℝ) else 0)
            (fun q _ => by split <;> norm_num) hqS
          simpa [count,hqA] using hs
        have hm := mul_le_mul_of_nonneg_left hsingle hM
        simp only [htrue,↓reduceIte]
        exact (hcap e he).trans (by simpa using hm)
      · simp only [hp,hn,and_false,↓reduceIte]
        exact mul_nonneg hM (hcpos e)
    · simp [hp]
  have hs := Finset.sum_le_sum hterm
  have hid : (∑ e ∈ B, if p ∈ A e then count e else 0) =
      ∑ q ∈ S.erase p, pairCount B A p q := by
    simp only [pairCount]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hp : p ∈ A e
    · simp [count,hp]
    · simp [hp]
  unfold restrictionLoad
  calc
    _ ≤ ∑ e ∈ B, M*(if p ∈ A e then count e else 0) := hs
    _ = M*(∑ e ∈ B, if p ∈ A e then count e else 0) := by rw [Finset.mul_sum]
    _ = M*(∑ q ∈ S.erase p, pairCount B A p q) := by rw [hid]
    _ ≤ M*budget := mul_le_mul_of_nonneg_left hbudget hM

theorem odd_set_degree_budget (h mass degreeSum : ℝ)
    (hh : 3 ≤ h) (hhandshake : 2*mass ≤ degreeSum)
    (hdegree : degreeSum ≤ (2/3)*h) : mass ≤ (h-1)/2 := by
  linarith

#print axioms three_complement_intersection
#print axioms three_complement_incidence_count
#print axioms repair_margin
#print axioms peak_removal_margin
#print axioms actual_restriction_budget
#print axioms odd_set_degree_budget

end DiffuseFractionalCover
