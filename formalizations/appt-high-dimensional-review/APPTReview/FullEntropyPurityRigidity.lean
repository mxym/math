import APPTReview.FlatEntropyPurity

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

theorem stateExcessPurity_nonneg {m n : ℕ} (hm : 0<m) (hn : 0<n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hρ : APPT.Quantum.IsDensity A) :
    0≤stateExcessPurity A := by
  have hD : 0<Fintype.card (Fin m × Fin n) := by simpa using Nat.mul_pos hm hn
  have hi := ordered_variance_identity hD hρ.1.isHermitian.eigenvalues₀
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
  have hh : 0≤∑ i,(hρ.1.isHermitian.eigenvalues₀ i-1/(Fintype.card (Fin m × Fin n):ℝ))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [hi,← purity_eq_ordered_eigenvalues hρ.1.isHermitian] at hh
  exact mul_nonneg (sq_nonneg _) hh

/-- On flat density spectra, entropy and purity have the same normalized
second-order limit. Neither APPT nor asymptotic optimality is used here. -/
theorem flat_density_entropy_purity_limit_iff (k n : ℕ → ℕ) (K : ℝ) (hK : 0≤K)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hn : ∀ j,0<n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hflat : ∀ ε : ℝ,0<ε → ∀ᶠ j in atTop,∀ i,
      |(Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*(hρ j).1.isHermitian.eigenvalues₀ i-1|<ε) :
    Tendsto (fun j => 2*(Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j)) atTop (𝓝 K) ↔
      Tendsto (fun j => stateExcessPurity (A j)) atTop (𝓝 K) := by
  constructor
  · intro hE
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hKP : 0<K+2 := by linarith
    let δ := min ((ε/2)/(K+2)) (1/2)
    have hδ : 0<δ := lt_min (by positivity) (by norm_num)
    have hδ2 : δ≤1/2 := min_le_right _ _
    have hδ1 : δ<1 := by linarith
    have hεb : δ*(K+2)≤ε/2 := (le_div_iff₀ hKP).mp (min_le_left _ _)
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hE δ hδ
    obtain ⟨M,hM⟩ := (hflat δ hδ).exists_forall_of_atTop
    refine ⟨max M N,?_⟩
    intro j hj
    have hf := hM j ((le_max_left _ _).trans hj)
    have he := hN j ((le_max_right _ _).trans hj)
    rw [Real.dist_eq] at he ⊢
    have hb := density_flat_entropy_purity_bounds (by omega : 0<k j+2) (hn j) (hρ j) δ hδ.le hδ1 (fun i => (hf i).le)
    exact (flat_entropy_to_purity_error _ _ K δ hK hδ.le hδ2 hb.1 hb.2 he.le).trans_lt
      (hεb.trans_lt (by linarith))
  · intro hQ
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hKP : 0<2*K+3 := by linarith
    let δ := min ((ε/2)/(2*K+3)) (1/2)
    have hδ : 0<δ := lt_min (by positivity) (by norm_num)
    have hδ2 : δ≤1/2 := min_le_right _ _
    have hδ1 : δ<1 := by linarith
    have hεb : δ*(2*K+3)≤ε/2 := (le_div_iff₀ hKP).mp (min_le_left _ _)
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hQ δ hδ
    obtain ⟨M,hM⟩ := (hflat δ hδ).exists_forall_of_atTop
    refine ⟨max M N,?_⟩
    intro j hj
    have hf := hM j ((le_max_left _ _).trans hj)
    have hq := hN j ((le_max_right _ _).trans hj)
    rw [Real.dist_eq] at hq ⊢
    have hb := density_flat_entropy_purity_bounds (by omega : 0<k j+2) (hn j) (hρ j) δ hδ.le hδ1 (fun i => (hf i).le)
    have hnon := stateExcessPurity_nonneg (by omega : 0<k j+2) (hn j) (hρ j)
    exact (flat_purity_to_entropy_error _ _ K δ hnon hK hδ.le hδ2 hb.1 hb.2 hq.le).trans_lt
      (hεb.trans_lt (by linarith))

/-- Complete equivalence for saturation of the proposed sharp von Neumann
coefficient: it is exactly purity saturation plus uniform relative flatness.
This does not prove existence of a flat APPT attaining sequence. -/
theorem appt_entropy_saturation_iff_flat_purity (k n : ℕ → ℕ) (γ : ℝ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j,k j+2≤n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hP : ∀ j,APPT.Quantum.AbsolutelyPPT (A j))
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun j => (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j))
      atTop (𝓝 (max 8 (4+γ)/2)) ↔
    (Tendsto (fun j => stateExcessPurity (A j)) atTop (𝓝 (max 8 (4+γ))) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ j in atTop,∀ i,
        |(Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*(hρ j).1.isHermitian.eigenvalues₀ i-1|<ε) := by
  have hK : 0≤max (8:ℝ) (4+γ) := (by norm_num : (0:ℝ)≤8).trans (le_max_left _ _)
  have hn : ∀ j,0<n j := by intro j;have ht:=hmn j;omega
  constructor
  · intro he
    have hf := appt_full_entropy_saturation_flat k n γ A hmn hρ hP hk hratio he
    refine ⟨(flat_density_entropy_purity_limit_iff k n _ hK A hn hρ hf).mp ?_,hf⟩
    have hh := he.const_mul 2
    convert hh using 1
    · funext j;ring
    · ring
  · rintro ⟨hq,hf⟩
    have hh := (flat_density_entropy_purity_limit_iff k n _ hK A hn hρ hf).mpr hq
    have he := hh.div_const 2
    convert he using 1
    funext j
    ring

end APPTReview
