import OperationalCompletion.ReservedTrial
import OperationalCompletion.FidelityExponent
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem reserved_variational_exponential_lower (m n : ℕ) (hm : 2≤m) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ) (hR0 : 0≤R)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (-(k:ℝ)*(fidelityExponent hX.1.isHermitian.eigenvalues R+ε)) ≤
        (reservedProtocol m n k (K k) (by omega) (by omega) hmn (hK k)).fidelity
          (tensorInput m n k X) := by
  have hm0 : 0<m := by omega
  have hn0 : 0<n := by omega
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm0 hn0⟩⟩
  let p := hX.1.isHermitian.eigenvalues
  let A := Real.log m
  let L := Real.log m+Real.log n
  let c := cappedEntropyRate m n R
  let E := fidelityExponent p R
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  have hD : 2≤Fintype.card (Fin (m*n)) := by simp only [Fintype.card_fin]; nlinarith
  obtain ⟨q,hq,hqs,hSupport,hH,hnear⟩ := primal_near_minimizer_strict_entropy p hp hs hD c (ε/4) (by linarith)
  have hHL : entropy q<L := by
    have hmR : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm0
    have hnR : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn0
    simpa only [Fintype.card_fin,Nat.cast_mul,Real.log_mul hmR hnR] using hH
  have hA : 0<A := Real.log_pos (by exact_mod_cast (show 1<m by omega))
  let B := min R (min A ((L-entropy q)/2))
  have hid : divergence q p+R-B = max 0 (R-A)+primalObjective p c q :=
    trialWidth_primal_identity p q A L R
  have htrial : divergence q p+R-B≤E+ε/4 := by
    dsimp only [E,fidelityExponent]
    change divergence q p+R-B≤max 0 (R-A)+_+ε/4
    linarith
  by_cases hzero : R=0
  · have hB : B=0 := by
      dsimp [B]
      rw [hzero,min_eq_left (le_min hA.le (by linarith))]
    have hevent := reserved_trial_exponential_lower m n hm0 hn0 hmn K hK R hR X hX
      q hq hqs hSupport 0 le_rfl (Or.inr rfl) hA (by simpa only [mul_zero,sub_zero] using hHL)
      (ε/2) (by linarith)
    filter_upwards [hevent] with k hk
    apply (Real.exp_le_exp.mpr _).trans hk
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (Nat.cast_nonneg k))
    rw [hB] at htrial
    linarith
  · have hRpos : 0<R := lt_of_le_of_ne hR0 (Ne.symm hzero)
    have hBpos : 0<B := lt_min hRpos (lt_min hA (by linarith))
    let δ := min (B/2) (ε/4)
    have hδ : 0<δ := lt_min (by linarith) (by linarith)
    have hδB : δ≤B/2 := min_le_left _ _
    have hδε : δ≤ε/4 := min_le_right _ _
    let b := B-δ
    have hb : 0<b := by dsimp [b]; linarith
    have hbB : b<B := by dsimp [b]; linarith
    have hbR : b<R := hbB.trans_le (min_le_left _ _)
    have hbA : b<A := hbB.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hbH : entropy q<L-2*b := by
      have h := hbB.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    have hevent := reserved_trial_exponential_lower m n hm0 hn0 hmn K hK R hR X hX
      q hq hqs hSupport b hb.le (Or.inl hbR) hbA hbH (ε/4) (by linarith)
    filter_upwards [hevent] with k hk
    apply (Real.exp_le_exp.mpr _).trans hk
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (Nat.cast_nonneg k))
    dsimp [b]
    linarith

end
end OperationalCompletion
