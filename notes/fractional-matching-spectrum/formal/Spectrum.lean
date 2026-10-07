import FrontierCertificate

open scoped BigOperators
open SharpFractionalFrontier

namespace FractionalMatchingSpectrum

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

theorem anchored_frontier (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (P : ι) (r k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k) (hP : P ∈ E)
    (hPne : (A P).Nonempty) (hsize : (A P).card ≤ r)
    (hmeet : ∀ e ∈ E, e ≠ P → (A P ∩ A e).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1)
    (hmax : ∀ e ∈ E, y e ≤ y P) :
    mass E y ≤ max ((((k : ℝ)-1)*(r : ℝ)+1)/(k : ℝ))
      ((E.card : ℝ)/((k : ℝ)+1)) := by
  have hdata := incidence_bin_data E A y P r k hk hP hPne hsize hmeet hnonneg hfeas hmax
  have havg : mass E y ≤ (E.card : ℝ)*y P := by
    calc
      _ ≤ ∑ e ∈ E, y P := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hrR : 2 ≤ (r : ℝ) := by exact_mod_cast hr
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  exact three_peak_branches _ _ _ _ _ hrR hkR (Nat.cast_nonneg _)
    havg hdata.1 hdata.2

theorem anchor_pair (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (P e : ι) (hP : P ∈ E) (he : e ∈ E) (hne : e ≠ P)
    (hmeet : (A P ∩ A e).Nonempty)
    (hnonneg : ∀ f ∈ E, 0 ≤ y f)
    (hfeas : ∀ v, load E A y v ≤ 1) : y P+y e ≤ 1 := by
  obtain ⟨v,hv⟩ := hmeet
  obtain ⟨hvP,hve⟩ := Finset.mem_inter.mp hv
  have hsub : ({P,e} : Finset ι) ⊆ E := by
    intro f hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hP
    · exact he
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun f => if v ∈ A f then y f else (0 : ℝ)) hsub
    (fun f hf _ => by
      by_cases hvf : v ∈ A f
      · simpa [hvf] using hnonneg f hf
      · simp [hvf])
  have hPe : P ≠ e := Ne.symm hne
  simp only [Finset.sum_insert, Finset.mem_singleton, hPe, not_false_eq_true,
    Finset.sum_singleton, ite_eq_left hvP, ite_eq_left hve] at hs
  have hf := hfeas v
  unfold load at hf
  exact hs.trans hf

theorem anchored_half_bound (E : Finset ι) (A : ι → Finset V) (y : ι → ℝ)
    (P : ι) (hP : P ∈ E) (hcard : 2 ≤ E.card)
    (hmeet : ∀ e ∈ E, e ≠ P → (A P ∩ A e).Nonempty)
    (hnonneg : ∀ e ∈ E, 0 ≤ y e)
    (hfeas : ∀ v, load E A y v ≤ 1)
    (hmax : ∀ e ∈ E, y e ≤ y P) : mass E y ≤ (E.card : ℝ)/2 := by
  have hcardR : 2 ≤ (E.card : ℝ) := by exact_mod_cast hcard
  by_cases hb : y P ≤ 1/2
  · have havg : mass E y ≤ (E.card : ℝ)*y P := by
      calc
        _ ≤ ∑ e ∈ E, y P := Finset.sum_le_sum hmax
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg E.card : (0 : ℝ) ≤ _)
    nlinarith only [havg,hm]
  · have hs : (∑ e ∈ E.erase P, y e) ≤ (E.card : ℝ)-1-
        ((E.card : ℝ)-1)*y P := by
      have hu : (∑ e ∈ E.erase P, y e) ≤ ∑ e ∈ E.erase P, (1-y P) := by
        apply Finset.sum_le_sum
        intro e he
        have heE := Finset.mem_of_mem_erase he
        have hn := (Finset.mem_erase.mp he).1
        have hp := anchor_pair E A y P e hP heE hn (hmeet e heE hn) hnonneg hfeas
        linarith
      have hc := Finset.sum_erase_add E (fun _ => (1 : ℝ)) hP
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hu hc
      have hD : ((E.erase P).card : ℝ) = (E.card : ℝ)-1 := by linarith
      rw [hD] at hu
      nlinarith only [hu]
    have hsum := Finset.sum_erase_add E y hP
    change (∑ e ∈ E.erase P, y e)+y P = mass E y at hsum
    have hp := mul_nonneg (show 0 ≤ (E.card : ℝ)-2 by linarith)
      (show 0 ≤ y P-1/2 by linarith)
    nlinarith only [hs,hsum,hp]

#print axioms anchored_frontier
#print axioms anchor_pair
#print axioms anchored_half_bound

end FractionalMatchingSpectrum
