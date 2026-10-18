import OperationalCompletion.ReservedLimit
import OperationalCompletion.ErrorTail
import Spectrum.Direct
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem reserved_gaussian_lower (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (z : ℝ) (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (hC : (Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2<Real.log m)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k)-
      k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
      atTop (nhds z)) :
    (ProbabilityTheory.gaussianReal 0 (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real
      (Set.Iic (-2*z)) ≤ liminf (fun k =>
        (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X)) atTop := by
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  have hinfo := iidInformationEvent_gaussian_moving p hp hs hv
    (fun k => (k:ℝ)*reservationSafeCutoff m n k (K k)) (-2*z)
    (reservationSafeCutoff_gaussian m n hm hn K hK _ z hsecond)
  rw [←hinfo.liminf_eq]
  apply liminf_le_liminf _ hinfo.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop (fun k =>
      ((reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
        (tensorInput_density m n k X hX)).2))
  filter_upwards [eventually_gt_atTop 0,
    reservationCap_eventually m n hm hn K hK _ (secondOrder_rate K _ z hsecond) hC] with k hk hcap
  exact (iidInformationEvent_le_empiricalEntropyMass hk p hp hs _ _ le_rfl).trans
    (reservedProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX)

/-- The very same soft-grid family has the full Gaussian limit, with local
feasibility proved from the strict entropy-limited gap rather than assumed for
every finite target. -/
theorem reserved_gaussian_limit (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (z : ℝ) (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (hC : (Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2<Real.log m)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k)-
      k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
      atTop (nhds z)) :
    Tendsto (fun k => (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity
      (tensorInput m n k X)) atTop
      (nhds ((ProbabilityTheory.gaussianReal 0
        (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real (Set.Iic (-2*z)))) := by
  refine tendsto_of_le_liminf_of_limsup_le
    (reserved_gaussian_lower m n hm hn hmn K hK X hX z hv hC hsecond)
    (KrausPPTProtocol.tensor_gaussian_converse m n hm hn K hK _ X hX hv z hsecond) ?_ ?_
  · exact isBoundedUnder_of ⟨1,fun k =>
      ((reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
        (tensorInput_density m n k X hX)).2⟩
  · exact isBoundedUnder_of ⟨0,fun k =>
      ((reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
        (tensorInput_density m n k X hX)).1⟩

theorem reserved_strict_direct_error_upper (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hlo : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R)
    (hhi : Real.log m+Real.log n-2*R<Real.log X.rank) (η : ℝ) (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop,
      1-(reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X) ≤
        Real.exp (-(k:ℝ)*
          ((⨅ q : {q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues) //
            Real.log m+Real.log n-2*R≤entropy q.1},
              divergence q.1.1 (supportLaw hX.1.isHermitian.eigenvalues))-η)) := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  have hprob := density_empiricalEntropyError_strict_direct_exponential X hX
    (fun k => reservationSafeCutoff m n k (K k)) _
    (reservationSafeCutoff_tendsto m n hm hn K hK R hR) hlo hhi η hη
  filter_upwards [hprob,reservationCap_eventually m n hm hn K hK R hR hRm,eventually_gt_atTop 0]
    with k hbound hcap hk
  exact (sub_le_sub_left (reservedProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX) 1).trans hbound

end
end OperationalCompletion
