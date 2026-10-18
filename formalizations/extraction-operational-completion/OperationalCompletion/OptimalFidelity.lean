import OperationalCompletion.Reliability

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

def candidateFidelities {a b K : ℕ} (C : KrausPPTProtocol a b K → Prop)
    (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) : Set ℝ :=
  {y | ∃ V,C V ∧ y=V.fidelity X}

/-- The genuine supremum of the actual physical protocol class. No supplied
performance envelope is used as the definition of an optimal fidelity. -/
def protocolOptimum {a b K : ℕ} (C : KrausPPTProtocol a b K → Prop)
    (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) : ℝ := sSup (candidateFidelities C X)

theorem candidateFidelities_bddAbove {a b K : ℕ} (hK : 0<K)
    (C : KrausPPTProtocol a b K → Prop) (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hX : APPT.Quantum.IsDensity X) : BddAbove (candidateFidelities C X) := by
  refine ⟨1,?_⟩
  rintro y ⟨V,hV,rfl⟩
  exact (V.fidelity_bounds hK X hX).2

theorem protocolOptimum_ge {a b K : ℕ} (hK : 0<K)
    (C : KrausPPTProtocol a b K → Prop) (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (V : KrausPPTProtocol a b K) (hV : C V) :
    V.fidelity X≤protocolOptimum C X :=
  le_csSup (candidateFidelities_bddAbove hK C X hX) ⟨V,hV,rfl⟩

theorem protocolOptimum_le {a b K : ℕ}
    (C : KrausPPTProtocol a b K → Prop) (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (V₀ : KrausPPTProtocol a b K) (hV₀ : C V₀) (r : ℝ)
    (hbound : ∀ V,C V → V.fidelity X≤r) : protocolOptimum C X≤r := by
  unfold protocolOptimum
  have hnonempty : (candidateFidelities C X).Nonempty := ⟨V₀.fidelity X,V₀,hV₀,rfl⟩
  apply csSup_le hnonempty
  rintro y ⟨V,hV,rfl⟩
  exact hbound V hV

theorem protocolOptimum_bounds {a b K : ℕ} (hK : 0<K)
    (C : KrausPPTProtocol a b K → Prop) (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (V₀ : KrausPPTProtocol a b K) (hV₀ : C V₀) :
    0≤protocolOptimum C X ∧ protocolOptimum C X≤1 :=
  ⟨(V₀.fidelity_bounds hK X hX).1.trans (protocolOptimum_ge hK C X hX V₀ hV₀),
    protocolOptimum_le C X V₀ hV₀ 1 (fun V _ => (V.fidelity_bounds hK X hX).2)⟩

/-- Every actual sub-class of PPT protocols containing the common local grid
family has the same state-aware optimal strict-direct error exponent. This
includes the entire finite-Kraus PPT class and the complete product-local class. -/
theorem optimal_reliability_limit (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) (hRm : R<Real.log m)
    (C : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k) → Prop)
    (hC : ∀ k,C k (gridProtocol m n k (K k) hm hn hmn (hK k)))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hlo : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R)
    (hhi : Real.log m+Real.log n-2*R<Real.log X.rank) :
    Tendsto (fun k : ℕ => -Real.log (1-protocolOptimum (C k) (tensorInput m n k X))/k)
      atTop (nhds (strictDirectExponent hX.1.isHermitian.eigenvalues
        (Real.log m+Real.log n-2*R))) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [ppt_strict_direct_error_lower m n hm hn K hK R hR X hX hlo hhi η hη,
    grid_strict_direct_error_upper m n hm hn hmn K hK R hR hRm X hX hlo hhi η hη]
      with k hlo hhi
  constructor
  · have hsup := protocolOptimum_le (C k) (tensorInput m n k X)
      (gridProtocol m n k (K k) hm hn hmn (hK k)) (hC k)
      (1-Real.exp (-(k:ℝ)*(strictDirectExponent hX.1.isHermitian.eigenvalues
        (Real.log m+Real.log n-2*R)+η))) (fun V _ => by
        have h := hlo V
        linarith)
    linarith
  · exact (sub_le_sub_left (protocolOptimum_ge (hK k) (C k) (tensorInput m n k X)
      (tensorInput_density m n k X hX) _ (hC k)) 1).trans hhi

end
end OperationalCompletion
