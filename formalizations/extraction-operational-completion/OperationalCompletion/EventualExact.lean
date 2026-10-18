import OperationalCompletion.GridGaussian

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem entropy_le_log_positiveSupport (q p : ι → ℝ) (hq : ∀ i,0≤q i)
    (hqs : ∑ i,q i=1) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (hsupport : ∀ i,0<q i → 0<p i) :
    entropy q ≤ Real.log (Fintype.card (PositiveSupport p)) := by
  classical
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  let s := Fintype.card (PositiveSupport p)
  have hsR : (0:ℝ)<s := by exact_mod_cast Fintype.card_pos
  let u := fun i => if 0<p i then 1/(s:ℝ) else 0
  have hu (i) : 0≤u i := by unfold u; split <;> positivity
  have hus : ∑ i,u i=1 := by
    rw [show (∑ i,u i) = ∑ i : PositiveSupport p,u i.1 from
      (positiveSupport_sum p hp (fun x => if 0<x then 1/(s:ℝ) else 0) (by simp)).symm]
    have hu_on (i : PositiveSupport p) : u i.1=1/(s:ℝ) := if_pos i.2
    simp_rw [hu_on]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change (s:ℝ)*(1/(s:ℝ))=1
    field_simp
  have hqu (i) (hi : 0<q i) : 0<u i := by
    simp only [u,if_pos (hsupport i hi)]
    positivity
  have hdiv := divergence_nonneg_of_support q u hq hqs hu hus hqu
  have hcross : (∑ i,q i*Real.log (u i))=-Real.log (s:ℝ) := by
    calc
      _ = ∑ i,q i*(-Real.log (s:ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : q i=0
        · simp only [hi,zero_mul]
        · have hqi : 0<q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
          simp only [u,if_pos (hsupport i hqi),one_div,Real.log_inv]
      _ = _ := by rw [←Finset.sum_mul,hqs,one_mul]
  have hid : divergence q u = Real.log (s:ℝ)-entropy q := by
    rw [divergence,entropy_eq_neg_sum]
    simp only [mul_sub,Finset.sum_sub_distrib,hcross]
    ring
  rw [hid] at hdiv
  exact sub_nonneg.mp hdiv

theorem empiricalEntropyMass_eq_one_of_support (p : ι → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (k : ℕ) (hk : 0<k) (c : ℝ)
    (hc : Real.log (Fintype.card (PositiveSupport p))≤c) :
    empiricalEntropyMass p k c=1 := by
  classical
  unfold empiricalEntropyMass
  calc
    _ = ∑ w : Fin k → ι,iidLaw p k w := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hwnot
      apply le_antisymm _ (iidLaw_nonneg p hp k w)
      apply le_of_not_gt
      intro hw
      have hH := entropy_le_log_positiveSupport (empiricalLaw w) p
        (empiricalLaw_nonneg w) (empiricalLaw_sum hk w) hp hs
        (empirical_support_of_iidLaw_pos p hp w hw)
      exact hwnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH.trans hc⟩)
    _ = 1 := iidLaw_sum p hs k

/-- The same all-state soft-grid protocol is eventually exactly faithful below
the rank threshold. No limit-one surrogate is used for exact fidelity. -/
theorem grid_eventually_exact (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hRank : Real.log X.rank<Real.log m+Real.log n-2*R) :
    ∀ᶠ k : ℕ in atTop,
      (gridProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X)=1 := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  have hcut := (gridSafeCutoff_tendsto m n hm hn K hK R hR).eventually_const_lt hRank
  filter_upwards [hcut,gridCap_eventually m hm K hK R hR hRm,eventually_gt_atTop 0]
    with k hcut hcap hk
  have hmass := gridProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX
  have hr : Fintype.card (PositiveSupport hX.1.isHermitian.eigenvalues)=X.rank :=
    density_positiveSupport_card_eq_rank X hX.1
  have hmone := empiricalEntropyMass_eq_one_of_support hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg (density_eigenvalues_sum X hX) k hk (gridSafeCutoff m n k (K k)) (by
      rw [hr]
      exact hcut.le)
  rw [hmone] at hmass
  exact le_antisymm
    ((gridProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
      (tensorInput_density m n k X hX)).2 hmass

end
end OperationalCompletion
