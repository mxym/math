import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace FractionalDesignCore

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

def mass (E : Finset ι) (y : ι → ℝ) : ℝ := ∑ e ∈ E, y e

def load (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ) (v : V) : ℝ :=
  ∑ e ∈ E, if v ∈ A e then y e else 0

theorem weighted_star (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (P : ι) (r : ℕ) (hP : P ∈ E) (hsize : (A P).card = r)
    (hmeet : ∀ e ∈ E, e ≠ P → (A P ∩ A e).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1) :
    mass E y ≤ (r : ℝ) - ((r : ℝ) - 1) * y P := by
  have hsum : (∑ e ∈ E.erase P, y e) + y P = mass E y := by
    exact Finset.sum_erase_add E y hP
  have hcount : (∑ e ∈ E.erase P, y e) ≤
      ∑ e ∈ E.erase P, ∑ v ∈ A P, if v ∈ A e then y e else 0 := by
    apply Finset.sum_le_sum
    intro e he
    have heE := Finset.mem_of_mem_erase he
    have heP := (Finset.mem_erase.mp he).1
    obtain ⟨v, hv⟩ := hmeet e heE heP
    obtain ⟨hvP, hve⟩ := Finset.mem_inter.mp hv
    have hs := Finset.single_le_sum
      (f := fun w => if w ∈ A e then y e else (0 : ℝ))
      (fun w _ => by
        by_cases hw : w ∈ A e
        · simpa only [ite_eq_left hw] using hnonneg e heE
        · simp only [ite_eq_right hw, le_refl]) hvP
    simpa only [ite_eq_left hve] using hs
  rw [Finset.sum_comm] at hcount
  have hupper : (∑ v ∈ A P, ∑ e ∈ E.erase P,
      if v ∈ A e then y e else 0) ≤ (r : ℝ) * (1 - y P) := by
    calc
      _ ≤ ∑ v ∈ A P, (1 - y P) := by
        apply Finset.sum_le_sum
        intro v hv
        have hs := Finset.sum_erase_add E
          (fun e => if v ∈ A e then y e else (0 : ℝ)) hP
        have hf := hfeas v
        simp only [ite_eq_left hv] at hs
        unfold load at hf
        linarith
      _ = (r : ℝ) * (1 - y P) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hsize]
  linarith

omit [DecidableEq ι] in
theorem threshold_degree (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (k : ℕ) (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1) (v : V) :
    ((E.filter fun e => 1 < ((k : ℝ) + 1) * y e).filter
      fun e => v ∈ A e).card ≤ k := by
  let S := (E.filter fun e => 1 < ((k : ℝ) + 1) * y e).filter
    fun e => v ∈ A e
  let T := E.filter fun e => v ∈ A e
  have hST : S ⊆ T := by
    intro e he
    simp only [S, T, Finset.mem_filter] at he ⊢
    exact ⟨he.1.1, he.2⟩
  have hload : (∑ e ∈ S, y e) ≤ 1 := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hST
      (fun e he _ => hnonneg e (Finset.mem_filter.mp he).1)
    have hf := hfeas v
    simp only [load, ← Finset.sum_filter] at hf
    exact hs.trans hf
  change S.card ≤ k
  by_contra hn
  have hkS : k + 1 ≤ S.card := by omega
  have hsne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : (∑ e ∈ S, (1 : ℝ)) <
      ∑ e ∈ S, ((k : ℝ) + 1) * y e := by
    apply Finset.sum_lt_sum_of_nonempty hsne
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hcard : (k : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hkS
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum] at hstrict
  have hkpos : 0 ≤ (k : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hload hkpos
  nlinarith

omit [DecidableEq ι] in
theorem bad_mass_bound (E : Finset ι) (y : ι → ℝ) (k : ℕ) (b : ℝ)
    (hmax : ∀ e ∈ E, y e ≤ b) :
    (((E.filter fun e => ((k : ℝ) + 1) * y e ≤ 1).card : ℝ)) *
      (((k : ℝ) + 1) * b - 1) ≤
    ((k : ℝ) + 1) * ((E.card : ℝ) * b - mass E y) := by
  let B := E.filter fun e => ((k : ℝ) + 1) * y e ≤ 1
  have hlower : (∑ e ∈ B, (((k : ℝ) + 1) * b - 1)) ≤
      ∑ e ∈ B, ((k : ℝ) + 1) * (b - y e) := by
    apply Finset.sum_le_sum
    intro e he
    have hy := (Finset.mem_filter.mp he).2
    linarith
  have hupper : (∑ e ∈ B, (b - y e)) ≤ ∑ e ∈ E, (b - y e) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro e he _
    exact sub_nonneg.mpr (hmax e he)
  have hkpos : 0 ≤ (k : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hupper hkpos
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hlower
  have htotal : (∑ e ∈ E, (b - y e)) = (E.card : ℝ) * b - mass E y := by
    simp [mass, Finset.sum_sub_distrib]
  rw [htotal] at hmul
  exact hlower.trans hmul

theorem extraction_algebra (m r k Y b s : ℝ)
    (hm : 0 ≤ m) (hr : 1 ≤ r) (hk : 0 ≤ k) (hs : 0 ≤ s)
    (hstar : Y ≤ r - (r - 1) * b) (haverage : Y ≤ m * b)
    (hbad : s * ((k + 1) * b - 1) ≤ (k + 1) * (m * b - Y)) :
    (r - 1) * ((k + 1) * Y - m) * s ≤
      m * (k + 1) * (m * r - (m + r - 1) * Y) := by
  have h0 : 0 ≤ m * (k + 1) := mul_nonneg hm (by linarith)
  have h1 := mul_nonneg (show 0 ≤ (k + 1) * s by positivity)
    (sub_nonneg.mpr haverage)
  have h2 := mul_nonneg hm (sub_nonneg.mpr hbad)
  have h3 : ((k + 1) * Y - m) * s ≤ m * (k + 1) * (m * b - Y) := by
    nlinarith only [h1, h2]
  have h4 := mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr hr)
  have h5 := mul_nonneg h0 (sub_nonneg.mpr hstar)
  have h6 := mul_nonneg hm (sub_nonneg.mpr hstar)
  have h7 : (r - 1) * (m * b - Y) ≤ m * r - (m + r - 1) * Y := by
    nlinarith only [h6]
  have h8 := mul_le_mul_of_nonneg_left h7 h0
  nlinarith only [h4, h8]

theorem incidence_extraction (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (r k : ℕ) (hr : 2 ≤ r) (hne : E.Nonempty)
    (huniform : ∀ e ∈ E, (A e).card = r)
    (hinter : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → (A e ∩ A f).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1) :
    ((r : ℝ) - 1) * (((k : ℝ) + 1) * mass E y - (E.card : ℝ)) *
      (((E.filter fun e => ((k : ℝ) + 1) * y e ≤ 1).card : ℝ)) ≤
      (E.card : ℝ) * ((k : ℝ) + 1) *
        ((E.card : ℝ) * (r : ℝ) - ((E.card : ℝ) + (r : ℝ) - 1) * mass E y) := by
  obtain ⟨P, hP, hmax⟩ := E.exists_max_image y hne
  have hstar := weighted_star E A y P r hP (huniform P hP)
    (fun e he hn => hinter P hP e he (Ne.symm hn)) hnonneg hfeas
  have havg : mass E y ≤ (E.card : ℝ) * y P := by
    calc
      _ ≤ ∑ e ∈ E, y P := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hbad := bad_mass_bound E y k (y P) hmax
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  exact extraction_algebra _ _ _ _ _ _ (Nat.cast_nonneg _) hr'
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hstar havg hbad

theorem capped_core_feasible (E C : Finset ι) (A : ι → Finset V)
    (k : ℕ) (hk : 0 < k) (hCE : C ⊆ E)
    (hcap : ∀ v, (C.filter fun e => v ∈ A e).card ≤ k) :
    ∀ v, load E A (fun e => if e ∈ C then 1 / (k : ℝ) else 0) v ≤ 1 := by
  intro v
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsum : load E A (fun e => if e ∈ C then 1 / (k : ℝ) else 0) v =
      ((C.filter fun e => v ∈ A e).card : ℝ) / (k : ℝ) := by
    unfold load
    have heq : (fun e => if v ∈ A e then (if e ∈ C then 1 / (k : ℝ) else 0) else 0) =
        (fun e => if e ∈ C.filter (fun e => v ∈ A e) then 1 / (k : ℝ) else 0) := by
      funext e
      by_cases he : e ∈ C <;> by_cases hv : v ∈ A e <;> simp [he, hv]
    rw [heq, ← Finset.sum_filter]
    have hf : E.filter (fun e => e ∈ C.filter (fun e => v ∈ A e)) =
        C.filter (fun e => v ∈ A e) := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hCE h.1, h⟩
    rw [hf]
    simp [div_eq_mul_inv]
  rw [hsum]
  have hc : ((C.filter fun e => v ∈ A e).card : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hcap v
  exact (div_le_one hkR).mpr hc

theorem capped_core_mass (E C : Finset ι) (k : ℕ) (hCE : C ⊆ E) :
    mass E (fun e => if e ∈ C then 1 / (k : ℝ) else 0) =
      (C.card : ℝ) / (k : ℝ) := by
  unfold mass
  rw [← Finset.sum_filter]
  have hf : E.filter (fun e => e ∈ C) = C := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hCE h, h⟩⟩
  rw [hf]
  simp [div_eq_mul_inv]

#print axioms weighted_star
#print axioms threshold_degree
#print axioms bad_mass_bound
#print axioms extraction_algebra
#print axioms incidence_extraction
#print axioms capped_core_feasible
#print axioms capped_core_mass

end FractionalDesignCore
