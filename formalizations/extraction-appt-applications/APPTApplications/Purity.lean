import APPTApplications.Capacity
import APPT.Quantum.SpectralMoment

open scoped BigOperators ComplexOrder Topology
open Matrix ExtractionSpectrum
namespace ExtractionAPPT
noncomputable section
variable {ι : Type} [Fintype ι]

/-- The collision sum of a normalized nonnegative law is strictly positive. -/
theorem collision_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    0 < ∑ i, (p i)^2 := by
  have hex : ∃ i, 0 < p i := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_nonpos (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hn i)
    rw [hs] at hh
    norm_num at hh
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => sq_nonneg (p j)) ⟨i,Finset.mem_univ _,pow_pos hi 2⟩

/-- Shannon entropy dominates collision entropy, including every zero atom.
The logarithm tangent bound is applied to the actual normalized collision sum. -/
theorem entropy_ge_neg_log_collision (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : -Real.log (∑ i, (p i)^2) ≤ entropy p := by
  let Q := ∑ i, (p i)^2
  have hQ : 0 < Q := collision_pos p hp hs
  have hi (i : ι) : p i * Real.log (p i / Q) ≤ p i * (p i / Q - 1) := by
    by_cases hz : p i = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (lt_of_le_of_ne (hp i) (Ne.symm hz)) hQ)) (hp i)
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hi i)
  have hright : (∑ i, p i * (p i / Q - 1)) = 0 := by
    simp only [mul_sub, ← mul_div_assoc, mul_one, ← pow_two, Finset.sum_sub_distrib,
      ← Finset.sum_div, hs]
    change Q / Q - 1 = 0
    rw [div_self hQ.ne', sub_self]
  have hleft : (∑ i, p i * Real.log (p i / Q)) = -entropy p - Real.log Q := by
    have he (i : ι) : p i * Real.log (p i / Q) = p i * Real.log (p i) - p i * Real.log Q := by
      by_cases hz : p i = 0
      · simp [hz]
      · rw [Real.log_div hz hQ.ne', mul_sub]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul,
      entropy, finiteMean, selfInformation, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [hright,hleft] at hb
  linarith

theorem purity_eq_spectral {m n : ℕ}
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hA : A.IsHermitian) :
    APPT.Quantum.purity A = ∑ i, (hA.eigenvalues i)^2 := by
  unfold APPT.Quantum.purity
  rw [APPT.Quantum.trace_square_eq_eigenvalues_square A hA, Complex.re_sum]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Pointwise comparison on every physical density matrix. -/
theorem density_entropy_purity_bound {m n : ℕ}
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hA : APPT.Quantum.IsDensity A) :
    0 < APPT.Quantum.purity A ∧ -Real.log (APPT.Quantum.purity A) ≤ quantumEntropy A := by
  have hs : ∑ i, hA.1.isHermitian.eigenvalues i = 1 := density_eigenvalues_sum A hA
  rw [purity_eq_spectral A hA.1.isHermitian, quantumEntropy_eq_spectral A hA.1.isHermitian]
  exact ⟨collision_pos _ hA.1.eigenvalues_nonneg hs,
    entropy_ge_neg_log_collision _ hA.1.eigenvalues_nonneg hs⟩

theorem physicalCapacity_le_purity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hA : APPT.Quantum.IsDensity A) :
    physicalCapacity m n A ≤ Real.log ((m:ℝ)*n*APPT.Quantum.purity A)/2 := by
  have hp := density_entropy_purity_bound A hA
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [physicalCapacity_eq hm hn hmn A hA,
    Real.log_mul (mul_pos hmR hnR).ne' hp.1.ne']
  exact (min_le_right _ _).trans (by linarith [hp.2])

/-- The comparison uses the existing attained purity supremum of the actual
APPT state set, without replacing it by a spectral relaxation. -/
theorem apptMaxCapacity_le_puritySup {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    apptMaxCapacity m n ≤ Real.log ((m:ℝ)*n*APPTReview.apptPuritySup m n)/2 := by
  obtain ⟨A,hA,_,hC⟩ := exists_appt_capacity_eq_sup hm hmn
  rw [←hC]
  have hp : APPT.Quantum.purity A ≤ APPTReview.apptPuritySup m n :=
    (APPTReview.appt_purity_sup_isGreatest hm hmn).2 ⟨A,hA.1,hA.2,rfl⟩
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (physicalCapacity_le_purity (by omega) (by omega) hmn A hA.1).trans
    (div_le_div_of_nonneg_right (Real.log_le_log
      (mul_pos (mul_pos hmR hnR) (density_entropy_purity_bound A hA.1).1)
      (mul_le_mul_of_nonneg_left hp (mul_pos hmR hnR).le)) (by norm_num))

end
end ExtractionAPPT
