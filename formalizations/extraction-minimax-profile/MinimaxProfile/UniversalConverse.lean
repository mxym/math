import MinimaxProfile.UniversalLimit
import Spectrum.ConverseLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter SymmetricSupport ExtractionSpectrum
namespace MinimaxProfile
noncomputable section

theorem tensorInput_spectral (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.IsHermitian) :
    let e := (SpectralProtocol.bipartitePowerCoordinates m n k).symm
    let V := reindexUnitary e (tensorUnitary hX.eigenvectorUnitary k)
    tensorInput m n k X = (V : Matrix _ _ ℂ) *
      Matrix.diagonal (fun w => (iidLaw hX.eigenvalues k (e w) : ℂ)) *
      (V : Matrix _ _ ℂ)ᴴ := by
  classical
  dsimp only
  unfold tensorInput SpectralProtocol.bipartitePowerTransport
  rw [tensorMatrix_spectral X hX k]
  change _ = ((tensorUnitary hX.eigenvectorUnitary k : Matrix _ _ ℂ).submatrix
      (SpectralProtocol.bipartitePowerCoordinates m n k).symm
      (SpectralProtocol.bipartitePowerCoordinates m n k).symm) * _ *
      ((tensorUnitary hX.eigenvectorUnitary k : Matrix _ _ ℂ).submatrix
      (SpectralProtocol.bipartitePowerCoordinates m n k).symm
      (SpectralProtocol.bipartitePowerCoordinates m n k).symm)ᴴ
  rw [Matrix.conjTranspose_submatrix]
  have hd := Matrix.submatrix_diagonal_equiv (fun w => (iidLaw hX.eigenvalues k w : ℂ))
    (SpectralProtocol.bipartitePowerCoordinates m n k).symm
  dsimp only [Function.comp_def] at hd
  rw [← hd, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

def tensorBudget (m n k K : ℕ) : ℝ := (m:ℝ)^k * (n:ℝ)^k / (K:ℝ)^2

/-- The finite converse applies to exactly the same tensor coordinates and
actual protocol class as the universal lower construction. -/
theorem KrausPPTProtocol.tensor_information_bound (m n k K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hK : 0 < K)
    (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (t : ℝ) : V.fidelity (tensorInput m n k X) ≤
      iidInformationEvent hX.1.isHermitian.eigenvalues k
        (Real.log (tensorBudget m n k K) + t) + Real.exp (-t/2) := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  letI : Nonempty (Fin (m^k)) := ⟨⟨0,Nat.pow_pos hm⟩⟩
  letI : Nonempty (Fin (n^k)) := ⟨⟨0,Nat.pow_pos hn⟩⟩
  let e := (SpectralProtocol.bipartitePowerCoordinates m n k).symm
  let p := hX.1.isHermitian.eigenvalues
  let q := iidLaw p k ∘ e
  let W := reindexUnitary e (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k)
  have hqs : ∑ w, q w = 1 := by
    change ∑ w, iidLaw p k (e w) = 1
    rw [e.sum_comp]
    exact iidLaw_sum p (density_eigenvalues_sum X hX) k
  have hqp (w) : 0 ≤ q w := iidLaw_nonneg p (fun i => hX.1.eigenvalues_nonneg i) k _
  have hsp : (V.U : Matrix _ _ ℂ) * tensorInput m n k X * (V.U : Matrix _ _ ℂ)ᴴ =
      ((V.U * W : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        Matrix.diagonal (fun w => (q w : ℂ)) *
      ((V.U * W : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)ᴴ := by
    rw [tensorInput_spectral m n k X hX.1.isHermitian]
    simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  unfold KrausPPTProtocol.fidelity overlap
  rw [Extraction.target_overlap_eq, hsp]
  have hM := Extraction.targetEffect_rains V.A V.complete V.ptPositive
  have hb : (Extraction.targetEffect V.A * Extraction.targetEffect V.A).trace.re ≤
      tensorBudget m n k K := by
    simpa only [tensorBudget, Fintype.card_fin, Nat.cast_pow] using
      (Extraction.rainsEffect_trace_square_le _ _ hM)
  have h := diagonalized_effect_information_bound q hqp hqs (V.U * W)
    (Extraction.targetEffect V.A) hM.1 hM.2.1 _ t (by
      unfold tensorBudget
      positivity) hb
  rw [informationMass_reindex (iidLaw p k) e,
    informationMass_iidLaw p (fun i => hX.1.eigenvalues_nonneg i) k] at h
  exact h

theorem tensorBudget_log (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n) (hK : 0 < K) :
    Real.log (tensorBudget m n k K) =
      (k:ℝ)*(Real.log m+Real.log n)-2*Real.log K := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  rw [tensorBudget, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  ring

theorem KrausPPTProtocol.tensor_gaussian_converse (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k)
    (V : ∀ k, KrausPPTProtocol (m^k) (n^k) (K k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues) (z : ℝ)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k) -
      k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
      atTop (nhds z)) :
    limsup (fun k => (V k).fidelity (tensorInput m n k X)) atTop ≤
      (ProbabilityTheory.gaussianReal 0 (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real
        (Set.Iic (-2*z)) := by
  have hh := (hsecond.const_mul (-2)).add gaussianSmoothing_div_sqrt_tendsto
  have hcut : Tendsto (fun k : ℕ => (Real.log (tensorBudget m n k (K k)) +
      gaussianSmoothing k-k*entropy hX.1.isHermitian.eigenvalues)/Real.sqrt k)
      atTop (nhds (-2*z)) := by
    apply (show Tendsto _ atTop (nhds (-2*z)) from by simpa only [add_zero] using hh).congr'
    filter_upwards with k
    rw [tensorBudget_log m n k (K k) hm hn (hK k)]
    ring
  exact information_bound_limsup_gaussian hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv
    (fun k => (V k).fidelity (tensorInput m n k X))
    (fun k => tensorBudget m n k (K k)) gaussianSmoothing (-2*z)
    (fun k => ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).1)
    (fun k t => (V k).tensor_information_bound m n k (K k) hm hn (hK k) X hX t)
    gaussianSmoothing_tendsto hcut

/-- A density-independent actual protocol family attains the full Gaussian
limit simultaneously for every fixed density with positive varentropy. -/
theorem universal_gaussian_limit (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (hKa : ∀ k, K k ≤ m^k) (hKb : ∀ k, K k ≤ n^k) :
    ∃ V : ∀ k, KrausPPTProtocol (m^k) (n^k) (K k),
      (∀ k, (V k).IsProductLocal) ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
        (z : ℝ), 0 < varentropy hX.1.isHermitian.eigenvalues →
        Tendsto (fun k : ℕ => (Real.log (K k) -
          k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
          atTop (nhds z) →
        Tendsto (fun k => (V k).fidelity (tensorInput m n k X)) atTop
          (nhds ((ProbabilityTheory.gaussianReal 0
            (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real (Set.Iic (-2*z)))) := by
  obtain ⟨V,hLocal,hV⟩ := universal_gaussian_lower m n hm hn K hK hKa hKb
  refine ⟨V,hLocal,?_⟩
  intro X hX z hv hsecond
  refine tendsto_of_le_liminf_of_limsup_le (hV X hX z hv hsecond)
    (KrausPPTProtocol.tensor_gaussian_converse m n hm hn K hK V X hX hv z hsecond) ?_ ?_
  · exact isBoundedUnder_of ⟨1, fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).2⟩
  · exact isBoundedUnder_of ⟨0, fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).1⟩

theorem tensorBudget_rate_limit (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k : ℕ => Real.log (tensorBudget m n k (K k))/k) atTop
      (nhds (Real.log m+Real.log n-2*R)) := by
  have h := (tendsto_const_nhds (x := Real.log m+Real.log n)).sub (hR.const_mul 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [tensorBudget_log m n k (K k) hm hn (hK k)]
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

/-- Every actual finite-Kraus PPT protocol sequence has fidelity tending to
zero above the entropy-limited rate, in the same model as the lower theorem. -/
theorem KrausPPTProtocol.tensor_rate_strong_converse (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k)
    (V : ∀ k, KrausPPTProtocol (m^k) (n^k) (K k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (habove : (Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2 < R) :
    Tendsto (fun k => (V k).fidelity (tensorInput m n k X)) atTop (nhds 0) := by
  exact information_bound_tendsto_zero hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX)
    (fun k => (V k).fidelity (tensorInput m n k X))
    (fun k => tensorBudget m n k (K k)) (Real.log m+Real.log n-2*R)
    (fun k => ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).1)
    (fun k t => (V k).tensor_information_bound m n k (K k) hm hn (hK k) X hX t)
    (tensorBudget_rate_limit m n hm hn K hK R hR) (by linarith)

end
end MinimaxProfile
