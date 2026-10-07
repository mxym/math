import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace SharpFractionalFrontier

theorem signed_bin (k n : ℕ) (b W : ℝ) (_hk : 2 ≤ k)
    (hlower : 1 ≤ ((k : ℝ)+1)*b) (hupper : (k : ℝ)*b ≤ 1)
    (hcount : W ≤ (n : ℝ)*b) (hcapacity : W ≤ 1-b) :
    W-(1-(k : ℝ)*b)*(n : ℝ) ≤
      ((k : ℝ)-1)*(((k : ℝ)+1)*b-1) := by
  by_cases hn : n < k
  · have hnk : (n : ℝ) ≤ (k : ℝ)-1 := by
      have hn' : n+1 ≤ k := by omega
      have hcast : (n : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast hn'
      linarith
    have hp := mul_nonneg (sub_nonneg.mpr hnk) (sub_nonneg.mpr hlower)
    nlinarith only [hcount,hp]
  · have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n by omega)
    have hp := mul_nonneg (sub_nonneg.mpr hkn) (sub_nonneg.mpr hupper)
    nlinarith only [hcapacity,hp]

theorem sum_signed_bins {V : Type*} (S : Finset V)
    (W : V → ℝ) (count : V → ℕ) (k : ℕ) (b : ℝ) (hk : 2 ≤ k)
    (hlower : 1 ≤ ((k : ℝ)+1)*b) (hupper : (k : ℝ)*b ≤ 1)
    (hcount : ∀ v ∈ S, W v ≤ (count v : ℝ)*b)
    (hcapacity : ∀ v ∈ S, W v ≤ 1-b) :
    (∑ v ∈ S, W v) - (1-(k : ℝ)*b)*(∑ v ∈ S, (count v : ℝ)) ≤
      (S.card : ℝ)*((k : ℝ)-1)*(((k : ℝ)+1)*b-1) := by
  have hs := Finset.sum_le_sum (fun v hv =>
    signed_bin k (count v) b (W v) hk hlower hupper (hcount v hv) (hcapacity v hv))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  nlinarith only [hs]

theorem signed_elimination (r k m Y b : ℝ)
    (h : (Y-b)-(1-k*b)*(m-1) ≤ r*(k-1)*((k+1)*b-1)) :
    Y ≤ m-((k-1)*r+1)+b*((k+1)*((k-1)*r+1)-k*m) := by
  nlinarith only [h]

theorem affine_endpoint_bound (k m g b Y : ℝ) (hk : 2 ≤ k)
    (hlower : 1 ≤ (k+1)*b) (hupper : k*b ≤ 1)
    (hY : Y ≤ m-g+b*((k+1)*g-k*m)) :
    Y ≤ max (g/k) (m/(k+1)) := by
  have hkpos : 0 < k := by linarith
  have hkp : 0 < k+1 := by linarith
  by_cases hsign : 0 ≤ (k+1)*g-k*m
  · have hp := mul_nonneg (sub_nonneg.mpr hupper) hsign
    have hy := mul_le_mul_of_nonneg_left hY (le_of_lt hkpos)
    have hg : Y*k ≤ g := by nlinarith only [hp,hy]
    exact ((le_div_iff₀ hkpos).mpr hg).trans (le_max_left _ _)
  · have hp := mul_nonneg (sub_nonneg.mpr hlower)
      (show 0 ≤ -((k+1)*g-k*m) by linarith)
    have hy := mul_le_mul_of_nonneg_left hY (le_of_lt hkp)
    have hm : Y*(k+1) ≤ m := by nlinarith only [hp,hy]
    exact ((le_div_iff₀ hkp).mpr hm).trans (le_max_right _ _)

theorem three_peak_branches (r k m Y b : ℝ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hm : 0 ≤ m) (haverage : Y ≤ m*b)
    (hstar : Y ≤ r-(r-1)*b)
    (hbin : 1 < (k+1)*b → k*b ≤ 1 →
      (Y-b)-(1-k*b)*(m-1) ≤ r*(k-1)*((k+1)*b-1)) :
    Y ≤ max (((k-1)*r+1)/k) (m/(k+1)) := by
  have hkpos : 0 < k := by linarith
  have hkp : 0 < k+1 := by linarith
  by_cases hsmall : (k+1)*b ≤ 1
  · have hp := mul_nonneg hm (sub_nonneg.mpr hsmall)
    have hy := mul_le_mul_of_nonneg_left haverage (le_of_lt hkp)
    have hmY : Y*(k+1) ≤ m := by nlinarith only [hp,hy]
    exact ((le_div_iff₀ hkp).mpr hmY).trans (le_max_right _ _)
  · have hlower : 1 < (k+1)*b := by linarith
    by_cases hupper : k*b ≤ 1
    · exact affine_endpoint_bound k m ((k-1)*r+1) b Y hk
        (le_of_lt hlower) hupper (signed_elimination _ _ _ _ _ (hbin hlower hupper))
    · have hp := mul_nonneg (show 0 ≤ r-1 by linarith)
        (show 0 ≤ k*b-1 by linarith)
      have hy := mul_le_mul_of_nonneg_left hstar (le_of_lt hkpos)
      have hg : Y*k ≤ (k-1)*r+1 := by nlinarith only [hp,hy]
      exact ((le_div_iff₀ hkpos).mpr hg).trans (le_max_left _ _)

theorem ramp_peak_control (r k m Y b d : ℝ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hd : 0 ≤ d) (hdef : (k+1)*(Y+d) = m)
    (hA : 0 < k*m-(k+1)*((k-1)*r+1))
    (hnear : (k*(k+1))*d < k*m-(k+1)*((k-1)*r+1))
    (hstar : Y ≤ r-(r-1)*b)
    (hbin : 1 < (k+1)*b → k*b ≤ 1 →
      (Y-b)-(1-k*b)*(m-1) ≤ r*(k-1)*((k+1)*b-1)) :
    k*b ≤ 1 ∧
      (k*m-(k+1)*((k-1)*r+1))*((k+1)*b-1) ≤ (k+1)*d := by
  have hkpos : 0 < k := by linarith
  have hkp : 0 < k+1 := by linarith
  have hupper : k*b ≤ 1 := by
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ r-1 by linarith)
      (show 0 ≤ k*b-1 by linarith)
    have hy := mul_le_mul_of_nonneg_left hstar (le_of_lt hkpos)
    have hg : Y*k ≤ (k-1)*r+1 := by nlinarith only [hp,hy]
    have hg' := mul_le_mul_of_nonneg_left hg (le_of_lt hkp)
    have heq := congrArg (fun x : ℝ => k*x) hdef
    nlinarith only [hg',heq,hnear]
  refine ⟨hupper, ?_⟩
  by_cases hsmall : (k+1)*b ≤ 1
  · have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA)
      (sub_nonpos.mpr hsmall)
    have hd' := mul_nonneg (le_of_lt hkp) hd
    exact hp.trans hd'
  · have hmid : 1 < (k+1)*b := by linarith
    have hy := signed_elimination r k m Y b (hbin hmid hupper)
    have hy' := mul_le_mul_of_nonneg_left hy (le_of_lt hkp)
    nlinarith only [hy',hdef]

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

def mass (E : Finset ι) (y : ι → ℝ) : ℝ := ∑ e ∈ E, y e

def load (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ) (v : V) : ℝ :=
  ∑ e ∈ E, if v ∈ A e then y e else 0

omit [DecidableEq ι] in
theorem assignment_sum (E : Finset ι) (S : Finset V) (f : ι → V)
    (z : ι → ℝ) (hf : ∀ e ∈ E, f e ∈ S) :
    (∑ v ∈ S, ∑ e ∈ E.filter (fun e => f e = v), z e) = ∑ e ∈ E, z e := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hs := Finset.sum_eq_single (f e)
    (s := S) (f := fun v => if f e = v then z e else (0 : ℝ))
    (fun v _ hn => by simp [Ne.symm hn])
    (fun hn => (hn (hf e he)).elim)
  simpa using hs

theorem incidence_bin_data (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (P : ι) (r k : ℕ) (hk : 2 ≤ k) (hP : P ∈ E)
    (hPne : (A P).Nonempty) (hsize : (A P).card ≤ r)
    (hmeet : ∀ e ∈ E, e ≠ P → (A P ∩ A e).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1)
    (hmax : ∀ e ∈ E, y e ≤ y P) :
    mass E y ≤ (r : ℝ)-((r : ℝ)-1)*y P ∧
    (1 < ((k : ℝ)+1)*y P → (k : ℝ)*y P ≤ 1 →
      (mass E y-y P)-(1-(k : ℝ)*y P)*((E.card : ℝ)-1) ≤
        (r : ℝ)*((k : ℝ)-1)*(((k : ℝ)+1)*y P-1)) := by
  classical
  let D := E.erase P
  obtain ⟨v0, hv0⟩ := hPne
  have hchoose : ∀ e, ∃ v : V, e ∈ D → v ∈ A P ∧ v ∈ A e := by
    intro e
    by_cases he : e ∈ D
    · obtain ⟨v,hv⟩ := hmeet e (Finset.mem_of_mem_erase he) (Finset.mem_erase.mp he).1
      exact ⟨v, fun _ => Finset.mem_inter.mp hv⟩
    · exact ⟨v0, fun hn => (he hn).elim⟩
  let f : ι → V := fun e => Classical.choose (hchoose e)
  have hf : ∀ e ∈ D, f e ∈ A P ∧ f e ∈ A e := by
    intro e he
    exact Classical.choose_spec (hchoose e) he
  let T : V → Finset ι := fun v => D.filter (fun e => f e = v)
  let W : V → ℝ := fun v => ∑ e ∈ T v, y e
  have hWnonneg : ∀ v, 0 ≤ W v := by
    intro v
    apply Finset.sum_nonneg
    intro e he
    exact hnonneg e (Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1)
  have hWcount : ∀ v ∈ A P, W v ≤ ((T v).card : ℝ)*y P := by
    intro v _
    calc
      _ ≤ ∑ e ∈ T v, y P := by
        apply Finset.sum_le_sum
        intro e he
        exact hmax e (Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1)
      _ = _ := by simp
  have hcap : ∀ v ∈ A P, W v ≤ 1-y P := by
    intro v hv
    have hle : W v ≤ ∑ e ∈ D, if v ∈ A e then y e else 0 := by
      simp only [W, T, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro e he
      by_cases heq : f e = v
      · have hve : v ∈ A e := heq ▸ (hf e he).2
        simp [heq,hve]
      · simp only [ite_eq_right heq]
        by_cases hve : v ∈ A e
        · simpa [hve] using hnonneg e (Finset.mem_of_mem_erase he)
        · simp [hve]
    have hs := Finset.sum_erase_add E
      (fun e => if v ∈ A e then y e else (0 : ℝ)) hP
    simp only [ite_eq_left hv] at hs
    have hfe := hfeas v
    unfold load at hfe
    change (∑ e ∈ D, if v ∈ A e then y e else 0)+y P = _ at hs
    linarith
  have hmasses : (∑ v ∈ A P, W v) = mass E y-y P := by
    have hs := assignment_sum D (A P) f y (fun e he => (hf e he).1)
    have he := Finset.sum_erase_add E y hP
    change (∑ e ∈ D, y e)+y P = mass E y at he
    change (∑ v ∈ A P, W v) = ∑ e ∈ D, y e at hs
    linarith
  have hcounts : (∑ v ∈ A P, ((T v).card : ℝ)) = (E.card : ℝ)-1 := by
    have hs := assignment_sum D (A P) f (fun _ => (1 : ℝ))
      (fun e he => (hf e he).1)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
    have he := Finset.sum_erase_add E (fun _ => (1 : ℝ)) hP
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at he
    change (∑ v ∈ A P, ((T v).card : ℝ)) = (D.card : ℝ) at hs
    change (D.card : ℝ)+1 = (E.card : ℝ) at he
    linarith
  have hb : y P ≤ 1 := by
    have hc := hcap v0 hv0
    have hn := hWnonneg v0
    linarith
  have hsizeR : ((A P).card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hsize
  have hstar : mass E y ≤ (r : ℝ)-((r : ℝ)-1)*y P := by
    have hs := Finset.sum_le_sum hcap
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    have hm := mul_le_mul_of_nonneg_right hsizeR (sub_nonneg.mpr hb)
    nlinarith only [hs,hm,hmasses]
  refine ⟨hstar, ?_⟩
  intro hlower hupper
  have hs := sum_signed_bins (A P) W (fun v => (T v).card) k (y P) hk
    (le_of_lt hlower) hupper hWcount hcap
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hfactor : 0 ≤ ((k : ℝ)-1)*(((k : ℝ)+1)*y P-1) :=
    mul_nonneg (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right hsizeR hfactor
  rw [hmasses,hcounts] at hs
  calc
    _ ≤ ((A P).card : ℝ)*((k : ℝ)-1)*(((k : ℝ)+1)*y P-1) := hs
    _ ≤ _ := by simpa only [mul_assoc] using hm

theorem incidence_frontier (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) (hne : E.Nonempty)
    (hedge : ∀ e ∈ E, (A e).Nonempty)
    (hrank : ∀ e ∈ E, (A e).card ≤ r)
    (hinter : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → (A e ∩ A f).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1) :
    mass E y ≤ max ((((k : ℝ)-1)*(r : ℝ)+1)/(k : ℝ))
      ((E.card : ℝ)/((k : ℝ)+1)) := by
  obtain ⟨P,hP,hmax⟩ := E.exists_max_image y hne
  have hdata := incidence_bin_data E A y P r k hk hP (hedge P hP) (hrank P hP)
    (fun e he hn => hinter P hP e he (Ne.symm hn)) hnonneg hfeas hmax
  have havg : mass E y ≤ (E.card : ℝ)*y P := by
    calc
      _ ≤ ∑ e ∈ E, y P := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hrR : 2 ≤ (r : ℝ) := by exact_mod_cast hr
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  exact three_peak_branches _ _ _ _ _ hrR hkR (Nat.cast_nonneg _)
    havg hdata.1 hdata.2

#print axioms signed_bin
#print axioms sum_signed_bins
#print axioms signed_elimination
#print axioms affine_endpoint_bound
#print axioms three_peak_branches
#print axioms ramp_peak_control
#print axioms assignment_sum
#print axioms incidence_bin_data
#print axioms incidence_frontier

end SharpFractionalFrontier
