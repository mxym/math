import MinimaxProfile.UniversalCutoff

open scoped BigOperators ComplexOrder Topology
open Matrix Filter SymmetricSupport ExtractionSpectrum
namespace MinimaxProfile
noncomputable section

theorem symmetric_log_rank_div_sqrt (E : ℕ) (hE : 0 < E) :
    Tendsto (fun k : ℕ => Real.log ((symmetricProjector E k).rank:ℝ) / Real.sqrt k)
      atTop (nhds 0) := by
  have he := (symmetricProjector_log_rank_limit E hE).div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun k : ℕ => Real.log (k:ℝ) / Real.sqrt k) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  have hc : Tendsto (fun k : ℕ => Real.log ((E-1).factorial:ℝ) / Real.sqrt k)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (he.add (hl.const_mul ((E-1:ℕ):ℝ))).sub hc
  simp only [mul_zero, zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards with k
  simp only [Function.comp_apply]
  ring

theorem orbitOverhead_log_div_sqrt (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => Real.log (orbitOverhead D k) / Real.sqrt k) atTop (nhds 0) := by
  have h := (symmetric_log_rank_div_sqrt (D*D) (Nat.mul_pos hD hD)).add
    (log_succ_div_sqrt_tendsto_zero.const_mul (D:ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards with k
  have hr : (0:ℝ) < (symmetricProjector (D*D) k).rank := by
    exact_mod_cast symmetricProjector_rank_pos (D*D) k (Nat.mul_pos hD hD)
  rw [orbitOverhead, Real.log_mul (ne_of_gt hr) (by positivity), Real.log_pow]
  ring

theorem compression_loss_div_sqrt (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => (Real.log 4 + Real.log (orbitOverhead D k)) / Real.sqrt k)
      atTop (nhds 0) := by
  have hc : Tendsto (fun k : ℕ => Real.log 4 / Real.sqrt k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [add_div, add_zero] using hc.add (orbitOverhead_log_div_sqrt D hD)

theorem compression_loss_div_nat (D : ℕ) (hD : 0 < D) :
    Tendsto (fun k : ℕ => (Real.log 4 + Real.log (orbitOverhead D k)) / k)
      atTop (nhds 0) := by
  have hi : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (compression_loss_div_sqrt D hD).mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with k
  change ((Real.log 4 + Real.log (orbitOverhead D k)) / Real.sqrt k) / Real.sqrt k = _
  rw [div_div, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg k)]

theorem compressionCutoff_expansion (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk : 0 < k) (hK : 0 < K) :
    (k:ℝ)*compressionCutoff m n k K =
      (k:ℝ)*(Real.log m + Real.log n) - 2*Real.log K -
        (Real.log 4 + Real.log (orbitOverhead (m*n) k)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  rw [compressionCutoff_identity m n k K hk]
  push_cast
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity)]
  simp only [Real.log_pow]
  ring

theorem compressionCutoff_tendsto (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k) / k) atTop (nhds R)) :
    Tendsto (fun k => compressionCutoff m n k (K k)) atTop
      (nhds (Real.log m + Real.log n - 2*R)) := by
  have h := ((tendsto_const_nhds (x := Real.log m + Real.log n)).sub
    (hR.const_mul 2)).sub (compression_loss_div_nat (m*n) (Nat.mul_pos hm hn))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have he := compressionCutoff_expansion m n k (K k) hm hn hk (hK k)
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have heq : compressionCutoff m n k (K k) =
      (k*(Real.log m+Real.log n)-2*Real.log (K k)-
        (Real.log 4+Real.log (orbitOverhead (m*n) k))) / k := by
    exact (eq_div_iff hkR).2 (by simpa only [mul_comm] using he)
  rw [heq]
  field_simp
  <;> ring

theorem compressionCutoff_gaussian (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (H z : ℝ)
    (hsecond : Tendsto (fun k : ℕ =>
      (Real.log (K k) - k*((Real.log m+Real.log n-H)/2)) / Real.sqrt k)
      atTop (nhds z)) :
    Tendsto (fun k : ℕ =>
      (k*compressionCutoff m n k (K k) - k*H) / Real.sqrt k) atTop (nhds (-2*z)) := by
  have h := (hsecond.const_mul (-2)).sub (compression_loss_div_sqrt (m*n) (Nat.mul_pos hm hn))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [compressionCutoff_expansion m n k (K k) hm hn hk (hK k)]
  ring

theorem KrausPPTProtocol.fidelity_bounds {a b K : ℕ} (V : KrausPPTProtocol a b K)
    (hK : 0 < K) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hX : APPT.Quantum.IsDensity X) : 0 ≤ V.fidelity X ∧ V.fidelity X ≤ 1 := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  constructor
  · exact Extraction.positive_product_trace_re _ _
      (Extraction.bellProjector_density (d := Fin K)).1
      (Extraction.krausApply_posSemidef _ _ (hX.1.mul_mul_conjTranspose_same _))
  · have h := ExtractionLocalCap.kraus_target_overlap_full_envelope V.A V.complete
      V.ptPositive X hX V.U
    exact h.trans (min_le_left _ _)

private theorem default_protocol_exists (a b K : ℕ) (hK : 0 < K) :
    ∃ V : KrausPPTProtocol a b K, V.IsProductLocal := by
  obtain ⟨V,hLocal,_⟩ := projection_mass_protocol a b K hK 0 (by simp [Matrix.IsHermitian])
    (by simp) (by simp)
  exact ⟨V,hLocal⟩

def universalBlockProtocol (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k) : KrausPPTProtocol (m^k) (n^k) K :=
  if hk : 0 < k then
    (universal_compression_protocol m n k K hm hn hk hK hKa hKb).choose
  else (default_protocol_exists (m^k) (n^k) K hK).choose

theorem universalBlockProtocol_isProductLocal (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k) :
    (universalBlockProtocol m n k K hm hn hK hKa hKb).IsProductLocal := by
  by_cases hk : 0 < k
  · simp only [universalBlockProtocol, dite_eq_left hk]
    exact (universal_compression_protocol m n k K hm hn hk hK hKa hKb).choose_spec.1
  · simp only [universalBlockProtocol, dite_eq_right hk]
    exact (default_protocol_exists (m^k) (n^k) K hK).choose_spec

theorem universalBlockProtocol_mass (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk : 0 < k) (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    empiricalEntropyMass hX.1.isHermitian.eigenvalues k (compressionCutoff m n k K) ≤
      (universalBlockProtocol m n k K hm hn hK hKa hKb).fidelity (tensorInput m n k X) := by
  simp only [universalBlockProtocol, dif_pos hk]
  exact (universal_compression_protocol m n k K hm hn hk hK hKa hKb).choose_spec.2 X hX

/-- One protocol family, chosen without any density, attains unit fidelity
for every fixed density below its entropy-limited target rate. The natural
integer floors, polynomial orbit overhead and iid LLN are internal. -/
theorem universal_subcritical_rate (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (hKa : ∀ k, K k ≤ m^k) (hKb : ∀ k, K k ≤ n^k)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k) / k) atTop (nhds R)) :
    ∃ V : ∀ k, KrausPPTProtocol (m^k) (n^k) (K k),
      (∀ k, (V k).IsProductLocal) ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1),
        entropy hX.1.isHermitian.eigenvalues < Real.log m+Real.log n-2*R →
        Tendsto (fun k => (V k).fidelity (tensorInput m n k X)) atTop (nhds 1) := by
  let V := fun k => universalBlockProtocol m n k (K k) hm hn (hK k) (hKa k) (hKb k)
  refine ⟨V, fun k => universalBlockProtocol_isProductLocal m n k (K k) hm hn
    (hK k) (hKa k) (hKb k), ?_⟩
  intro X hX hH
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i, 0 ≤ p i := fun i => hX.1.eigenvalues_nonneg i
  have hs : ∑ i, p i = 1 := density_eigenvalues_sum X hX
  have hmass := empiricalEntropyMass_tendsto_one_moving p hp hs
    (fun k => compressionCutoff m n k (K k)) _ (compressionCutoff_tendsto m n hm hn K hK R hR) hH
  have hgap : Tendsto (fun k => 1-empiricalEntropyMass p k (compressionCutoff m n k (K k)))
      atTop (nhds 0) := by simpa only [sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hmass
  have hsmall : Tendsto (fun k => 1-(V k).fidelity (tensorInput m n k X)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun k => sub_nonneg.mpr
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).2)) _ hgap
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact sub_le_sub_left (universalBlockProtocol_mass m n k (K k) hm hn hk (hK k) (hKa k) (hKb k) X hX) 1
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub hsmall
  simpa only [sub_sub_cancel, sub_zero] using h

/-- The same density-independent family attains the Gaussian lower side for
every fixed actual input with positive varentropy. No CLT or iid hypothesis is
passed by the caller; both are proved for its actual eigenvalue law. -/
theorem universal_gaussian_lower (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (K : ℕ → ℕ) (hK : ∀ k, 0 < K k) (hKa : ∀ k, K k ≤ m^k) (hKb : ∀ k, K k ≤ n^k) :
    ∃ V : ∀ k, KrausPPTProtocol (m^k) (n^k) (K k),
      (∀ k, (V k).IsProductLocal) ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
        (z : ℝ), 0 < varentropy hX.1.isHermitian.eigenvalues →
        Tendsto (fun k : ℕ => (Real.log (K k) -
          k*((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2))/Real.sqrt k)
          atTop (nhds z) →
        (ProbabilityTheory.gaussianReal 0 (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real
          (Set.Iic (-2*z)) ≤ liminf (fun k => (V k).fidelity (tensorInput m n k X)) atTop := by
  let V := fun k => universalBlockProtocol m n k (K k) hm hn (hK k) (hKa k) (hKb k)
  refine ⟨V, fun k => universalBlockProtocol_isProductLocal m n k (K k) hm hn
    (hK k) (hKa k) (hKb k), ?_⟩
  intro X hX z hv hsecond
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i, 0 ≤ p i := fun i => hX.1.eigenvalues_nonneg i
  have hs : ∑ i, p i = 1 := density_eigenvalues_sum X hX
  have hinfo := iidInformationEvent_gaussian_moving p hp hs hv
    (fun k => (k:ℝ)*compressionCutoff m n k (K k)) (-2*z)
    (compressionCutoff_gaussian m n hm hn K hK _ z hsecond)
  rw [← hinfo.liminf_eq]
  apply liminf_le_liminf _ hinfo.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop (fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).2))
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (iidInformationEvent_le_empiricalEntropyMass hk p hp hs _ _ le_rfl).trans
    (universalBlockProtocol_mass m n k (K k) hm hn hk (hK k) (hKa k) (hKb k) X hX)

end
end MinimaxProfile
