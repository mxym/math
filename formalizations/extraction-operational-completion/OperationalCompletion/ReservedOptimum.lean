import OperationalCompletion.ReservedQuantile

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

/-- The genuine physical supremum has the same full Gaussian threshold as the
fixed common family, for every intermediate actual protocol class containing it. -/
theorem reserved_optimal_gaussian_limit (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (C : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k) → Prop)
    (hC : ∀ k,C k (reservedProtocol m n k (K k) hm hn hmn (hK k)))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (z : ℝ) (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (hCa : (Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2<Real.log m)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k)-
      k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
      atTop (nhds z)) :
    Tendsto (fun k => protocolOptimum (C k) (tensorInput m n k X)) atTop
      (nhds ((ProbabilityTheory.gaussianReal 0
        (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real (Set.Iic (-2*z)))) := by
  let F := fun k => protocolOptimum (C k) (tensorInput m n k X)
  have hbounds (k : ℕ) : 0≤F k ∧ F k≤1 :=
    protocolOptimum_bounds (hK k) (C k) _ (tensorInput_density m n k X hX) _ (hC k)
  have hh := (hsecond.const_mul (-2)).add gaussianSmoothing_div_sqrt_tendsto
  have hcut : Tendsto (fun k : ℕ => (Real.log (tensorBudget m n k (K k))+
      gaussianSmoothing k-k*entropy hX.1.isHermitian.eigenvalues)/Real.sqrt k)
      atTop (nhds (-2*z)) := by
    apply (show Tendsto _ atTop (nhds (-2*z)) from by simpa only [add_zero] using hh).congr'
    filter_upwards with k
    rw [tensorBudget_log m n k (K k) hm hn (hK k)]
    ring
  have hupper := information_bound_limsup_gaussian hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg (density_eigenvalues_sum X hX) hv F
    (fun k => tensorBudget m n k (K k)) gaussianSmoothing (-2*z)
    (fun k => (hbounds k).1) (fun k t =>
      protocolOptimum_le (C k) _ _ (hC k) _ (fun V _ =>
        V.tensor_information_bound m n k (K k) hm hn (hK k) X hX t))
    gaussianSmoothing_tendsto hcut
  have hcommon := reserved_gaussian_limit m n hm hn hmn K hK X hX z hv hCa hsecond
  have hlower : (ProbabilityTheory.gaussianReal 0
      (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real (Set.Iic (-2*z))≤liminf F atTop := by
    rw [←hcommon.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun k => protocolOptimum_ge (hK k)
      (C k) _ (tensorInput_density m n k X hX) _ (hC k))) hcommon.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop (fun k => (hbounds k).2))
  exact tendsto_of_le_liminf_of_limsup_le hlower hupper
    (isBoundedUnder_of ⟨1,fun k => (hbounds k).2⟩)
    (isBoundedUnder_of ⟨0,fun k => (hbounds k).1⟩)

end
end OperationalCompletion
