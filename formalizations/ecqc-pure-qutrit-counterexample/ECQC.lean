import QutritEntropy

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
noncomputable section

namespace ECQC.Qutrit

/-- All four actual measurement matrices form a complete MUB family. -/
theorem completeMUB : IsCompleteMUB basis :=
  ⟨basis_orthonormal, basis_mutually_unbiased⟩

/-- Every choice of three of the four settings gives the same retained sum. -/
theorem retained_sum (s : Finset (Fin 4)) (hs : s.card = 3) :
    (∑ a ∈ s, mutualInformation (bornTable rho (basis a) (basis a))) = 3 * Real.log 2 := by
  simp [measured_mutual_information, hs, nsmul_eq_mul]

/-- The entire value set in the original minimum is a nonempty singleton. -/
theorem retainedValues_singleton : retainedValues rho basis = {3 * Real.log 2} := by
  ext t
  constructor
  · rintro ⟨s, hs, ht⟩
    exact Set.mem_singleton_iff.mpr (ht.trans (retained_sum s hs))
  · intro ht
    refine ⟨{0,1,2}, by decide, ?_⟩
    exact (Set.mem_singleton_iff.mp ht).trans (retained_sum {0,1,2} (by decide)).symm

/-- The original ECQC minimum, not a selected or assumed subset score. -/
theorem ecqc_score_eq : ecqcScore rho basis = 3 * Real.log 2 := by
  rw [ecqcScore, retainedValues_singleton, csInf_singleton]

theorem ecqc_minimum_attained :
    ∃ s : Finset (Fin 4), s.card = 3 ∧
      (∑ a ∈ s, mutualInformation (bornTable rho (basis a) (basis a))) = ecqcScore rho basis := by
  refine ⟨{0,1,2}, by decide, ?_⟩
  rw [retained_sum _ (by decide), ecqc_score_eq]

/-- The strict excess of the actual ECQC score over quantum mutual information. -/
theorem exact_excess : ecqcScore rho basis - quantumMutualInformation rho = Real.log 2 := by
  rw [ecqc_score_eq, rho_quantum_mutual_information]
  ring

theorem strict_violation : quantumMutualInformation rho < ecqcScore rho basis := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [ecqc_score_eq, rho_quantum_mutual_information]
  linarith

/-- Complete explicit counterexample: a normalized pure state, actual density,
actual MUBs, spectral quantum information, exact minimum, and strict violation. -/
theorem pure_qutrit_counterexample :
    dotProduct (star psi) psi = 1 ∧
    rho = pureState psi ∧ IsDensity rho ∧
    IsCompleteMUB basis ∧
    quantumMutualInformation rho = 2 * Real.log 2 ∧
    ecqcScore rho basis = 3 * Real.log 2 ∧
    quantumMutualInformation rho < ecqcScore rho basis :=
  ⟨psi_normalized, rfl, rho_density, completeMUB,
    rho_quantum_mutual_information, ecqc_score_eq, strict_violation⟩

/-- Existential form over the original vector and measurement-matrix objects. -/
theorem exists_pure_qutrit_counterexample :
    ∃ (v : QQ → ℂ) (B : Fin 4 → Matrix Q Q ℂ),
      dotProduct (star v) v = 1 ∧ IsDensity (pureState v) ∧ IsCompleteMUB B ∧
      quantumMutualInformation (pureState v) < ecqcScore (pureState v) B :=
  ⟨psi, basis, psi_normalized, rho_density, completeMUB, strict_violation⟩

/-- The prime-dimensional pure-state ECQC universal statement is false.
There are no unproved entropy, basis, or probability hypotheses. -/
theorem pure_prime_dimensional_ecqc_is_false :
    ¬ (∀ (d : ℕ), d.Prime →
      ∀ (v : (Fin d × Fin d) → ℂ), dotProduct (star v) v = 1 →
      ∀ (B : Fin (d+1) → Matrix (Fin d) (Fin d) ℂ), IsCompleteMUB B →
        ecqcScore (pureState v) B ≤ quantumMutualInformation (pureState v)) := by
  intro h
  have hc := h 3 (by norm_num) psi psi_normalized basis completeMUB
  exact (not_le_of_gt strict_violation) hc

end ECQC.Qutrit

#print axioms ECQC.Qutrit.pure_qutrit_counterexample
#print axioms ECQC.Qutrit.pure_prime_dimensional_ecqc_is_false
