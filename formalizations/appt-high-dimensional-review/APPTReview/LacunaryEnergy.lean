import APPTReview.LacunaryMeasure
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators
namespace APPTReview

/-- Square-root splitting with the nonnegative hypotheses explicit. -/
theorem sqrt_sum_le_sum_sqrt (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  have h0 := Real.sqrt_nonneg a
  have h1 := Real.sqrt_nonneg b
  have h2 := Real.sqrt_nonneg (a+b)
  have hsq0 := Real.sq_sqrt ha
  have hsq1 := Real.sq_sqrt hb
  have hsq2 := Real.sq_sqrt (add_nonneg ha hb)
  nlinarith [mul_nonneg h0 h1]

/-- The finite energy estimate separating off-diagonal probability from loop
atoms. No common optimizing vector or independent levelwise measure is assumed. -/
theorem lacunary_energy_budget {ι : Type*} (S : Finset ι) (e q l : ι → ℝ)
    (B : ℝ) (hB : 0≤B)
    (he : ∀ i∈S,0≤e i) (heB : ∀ i∈S,e i≤B)
    (hq : ∀ i∈S,0≤q i) (hl : ∀ i∈S,0≤l i)
    (hqs : (∑ i∈S,q i)≤1/4) (hls : (∑ i∈S,l i)≤1) :
    (∑ i∈S,Real.sqrt (e i*(q i+(l i)^2/2))) ≤
      Real.sqrt (∑ i∈S,e i)/2+Real.sqrt (B/2) := by
  have hsplit (i) (hi : i∈S) :
      Real.sqrt (e i*(q i+(l i)^2/2)) ≤
        Real.sqrt (e i)*Real.sqrt (q i)+Real.sqrt (e i/2)*l i := by
    have heq : e i*(q i+(l i)^2/2)=e i*q i+(e i/2)*(l i)^2 := by ring
    rw [heq]
    have ht := sqrt_sum_le_sum_sqrt (e i*q i) ((e i/2)*(l i)^2)
      (mul_nonneg (he i hi) (hq i hi)) (mul_nonneg (div_nonneg (he i hi) (by norm_num)) (sq_nonneg _))
    rwa [Real.sqrt_mul (he i hi),Real.sqrt_mul (div_nonneg (he i hi) (by norm_num)),
      Real.sqrt_sq (hl i hi)] at ht
  have hc := Real.sum_mul_le_sqrt_mul_sqrt S (fun i => Real.sqrt (e i)) (fun i => Real.sqrt (q i))
  have hse : (∑ i∈S,(Real.sqrt (e i))^2)=∑ i∈S,e i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (he i hi))
  have hsq : (∑ i∈S,(Real.sqrt (q i))^2)=∑ i∈S,q i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hq i hi))
  rw [hse,hsq] at hc
  have hqr : Real.sqrt (∑ i∈S,q i) ≤ 1/2 := by
    have hs := Real.sq_sqrt (Finset.sum_nonneg hq)
    have hn := Real.sqrt_nonneg (∑ i∈S,q i)
    nlinarith
  have hhead : (∑ i∈S,Real.sqrt (e i)*Real.sqrt (q i)) ≤ Real.sqrt (∑ i∈S,e i)/2 := by
    have hmul := mul_le_mul_of_nonneg_left hqr (Real.sqrt_nonneg (∑ i∈S,e i))
    exact hc.trans (by nlinarith)
  have hloops : (∑ i∈S,Real.sqrt (e i/2)*l i) ≤ Real.sqrt (B/2) := by
    calc
      _ ≤ ∑ i∈S,Real.sqrt (B/2)*l i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [heB i hi])) (hl i hi)
      _ = Real.sqrt (B/2)*(∑ i∈S,l i) := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt (B/2) := by nlinarith [Real.sqrt_nonneg (B/2)]
  have hh := Finset.sum_le_sum hsplit
  rw [Finset.sum_add_distrib] at hh
  linarith

end APPTReview
