import APPTApplications.Entropy
import OperationalCompletion.LOCCCapacity

open scoped BigOperators ComplexOrder Topology
open Matrix ExtractionSpectrum
namespace ExtractionAPPT
noncomputable section

/-- The actual faithful capacity: a supremum of rates achieved by finite
adaptive local-instrument protocols after the separately allowed global U. -/
def physicalCapacity (m n : ℕ) (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℝ :=
  OperationalCompletion.faithfulCapacity m n
    (fun _ _ V => ExtractionLOCC.IsFiniteLOCCProtocol V) (flatten m n A)

theorem physicalCapacity_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hA : APPT.Quantum.IsDensity A) :
    physicalCapacity m n A =
      min (Real.log m) ((Real.log (m*n) - quantumEntropy A)/2) := by
  rw [physicalCapacity, (OperationalCompletion.finiteLOCC_capacities m n hm hn hmn
    (flatten m n A) (flatten_density A hA)).1, flatten_spectral_entropy A hA,
    Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]

theorem physicalCapacity_eq_cPPT {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≤ n)
    (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hA : APPT.Quantum.IsDensity A) :
    physicalCapacity m n A = OperationalCompletion.faithfulCapacity m n
      (fun _ _ _ => True) (flatten m n A) := by
  rw [physicalCapacity_eq hm hn hmn A hA,
    (OperationalCompletion.cPPT_capacities m n hm hn hmn (flatten m n A)
      (flatten_density A hA)).1, flatten_spectral_entropy A hA,
    Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]

def apptCapacityValues (m n : ℕ) : Set ℝ :=
  physicalCapacity m n '' APPTReview.physicalAPPTStates m n

def apptMaxCapacity (m n : ℕ) : ℝ := sSup (apptCapacityValues m n)

/-- The actual APPT entropy optimizer simultaneously maximizes the true
attainable-rate supremum; all extrema are proved to be physically attained. -/
theorem exists_appt_capacity_isGreatest {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ A ∈ APPTReview.physicalAPPTStates m n,
      quantumEntropy A = apptMinEntropy m n ∧
      IsGreatest (apptCapacityValues m n) (physicalCapacity m n A) := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  obtain ⟨A,hA,hmin⟩ := exists_appt_entropy_isLeast hm hmn
  refine ⟨A,hA,hmin.csInf_eq.symm,⟨⟨A,hA,rfl⟩,?_⟩⟩
  rintro x ⟨B,hB,rfl⟩
  rw [physicalCapacity_eq hm0 hn0 hmn B hB.1, physicalCapacity_eq hm0 hn0 hmn A hA.1]
  exact min_le_min le_rfl (by linarith [hmin.2 ⟨B,hB,rfl⟩])

theorem exists_appt_capacity_eq_sup {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ A ∈ APPTReview.physicalAPPTStates m n,
      quantumEntropy A = apptMinEntropy m n ∧ physicalCapacity m n A = apptMaxCapacity m n := by
  obtain ⟨A,hA,hE,hmax⟩ := exists_appt_capacity_isGreatest hm hmn
  exact ⟨A,hA,hE,hmax.csSup_eq.symm⟩

/-- The application identity, with both the entropy minimum and the actual
capacity maximum represented by attained extrema on the physical APPT set. -/
theorem apptMaxCapacity_eq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    apptMaxCapacity m n =
      min (Real.log m) ((Real.log (m*n) - apptMinEntropy m n)/2) := by
  obtain ⟨A,hA,hE,hC⟩ := exists_appt_capacity_eq_sup hm hmn
  rw [← hC, physicalCapacity_eq (by omega) (by omega) hmn A hA.1, hE]

/-- The purity maximum in the comparison is the pre-existing genuine physical
maximum, and is attained by an actual APPT density matrix. -/
theorem exists_appt_purity_maximizer {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ A ∈ APPTReview.physicalAPPTStates m n,
      APPT.Quantum.purity A = APPTReview.apptPuritySup m n := by
  obtain ⟨A,hA,hP,hE⟩ := APPTReview.exists_appt_purity_eq_sup hm hmn
  exact ⟨A,⟨hA,hP⟩,hE⟩

end
end ExtractionAPPT
