import APPTReview.StateTopology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

open scoped BigOperators ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix Filter
namespace APPTReview

/-- Nonemptiness is witnessed by an actual, normalized, APPT projection state. -/
theorem physicalAPPTStates_nonempty {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    (physicalAPPTStates m n).Nonempty := by
  obtain ⟨A,hA,hP,_⟩ := exists_projectionPlateau hm (by omega : 0<n) 0 (by omega : 0≤m*n)
  exact ⟨A,hA,hP⟩

/-- Every continuous real objective has genuine extrema on the physical APPT set. -/
theorem continuous_objective_appt_extrema {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    (F : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ → ℝ) (hF : Continuous F) :
    (∃ A ∈ physicalAPPTStates m n, IsMaxOn F (physicalAPPTStates m n) A) ∧
    (∃ A ∈ physicalAPPTStates m n, IsMinOn F (physicalAPPTStates m n) A) := by
  have hc := isCompact_physicalAPPTStates m n
  have he := physicalAPPTStates_nonempty hm hmn
  exact ⟨hc.exists_isMaxOn he hF.continuousOn, hc.exists_isMinOn he hF.continuousOn⟩

/-- Existence of an attained maximum, not just a bounded supremum. -/
theorem exists_appt_purity_isGreatest {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      IsGreatest (apptPurityValues m n) (APPT.Quantum.purity A) := by
  obtain ⟨A,hA,hmax⟩ := (continuous_objective_appt_extrema hm hmn
    APPT.Quantum.purity continuous_quantum_purity).1
  refine ⟨A,hA.1,hA.2,⟨A,hA.1,hA.2,rfl⟩,?_⟩
  intro x hx
  obtain ⟨B,hB,hP,rfl⟩ := hx
  exact hmax ⟨hB,hP⟩

/-- The existing physical supremum equals the purity of an actual optimizer. -/
theorem exists_appt_purity_eq_sup {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      APPT.Quantum.purity A = apptPuritySup m n := by
  obtain ⟨A,hA,hP,hg⟩ := exists_appt_purity_isGreatest hm hmn
  have he := appt_purity_values_nonempty_bounded hm hmn
  refine ⟨A,hA,hP,le_antisymm (le_csSup he.2 hg.1) ?_⟩
  exact csSup_le he.1 hg.2

theorem appt_purity_sup_isGreatest {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    IsGreatest (apptPurityValues m n) (apptPuritySup m n) := by
  obtain ⟨A,hA,hP,he⟩ := exists_appt_purity_eq_sup hm hmn
  refine ⟨⟨A,hA,hP,he.symm⟩,?_⟩
  exact fun _ hx => le_csSup (appt_purity_values_nonempty_bounded hm hmn).2 hx

/-- Fixed-dimensional near-maximizers have a convergent physical optimizing subsequence.
This is not the unresolved compactness lemma for dimension-varying multiscale graphs. -/
theorem appt_near_maximizers_subsequence {m n : ℕ}
    (A : ℕ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hA : ∀ k, APPT.Quantum.IsDensity (A k) ∧ APPT.Quantum.AbsolutelyPPT (A k))
    (hpur : Tendsto (fun k => APPT.Quantum.purity (A k)) atTop (𝓝 (apptPuritySup m n))) :
    ∃ B : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity B ∧ APPT.Quantum.AbsolutelyPPT B ∧
      APPT.Quantum.purity B = apptPuritySup m n ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (A ∘ φ) atTop (𝓝 B) := by
  letI : FirstCountableTopology (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin m × Fin n → Fin m × Fin n → ℂ))
  obtain ⟨B,hB,φ,hφ,hconv⟩ := (isCompact_physicalAPPTStates m n).tendsto_subseq hA
  have h1 := continuous_quantum_purity.continuousAt.tendsto.comp hconv
  have h2 := hpur.comp hφ.tendsto_atTop
  have he : APPT.Quantum.purity B=apptPuritySup m n := tendsto_nhds_unique h1 h2
  exact ⟨B,hB.1,hB.2,he,φ,hφ,hconv⟩

end APPTReview
