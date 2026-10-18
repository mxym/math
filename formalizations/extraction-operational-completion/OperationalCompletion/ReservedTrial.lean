import OperationalCompletion.ReservedCoverage
import OperationalCompletion.ReservedLimit
import OperationalCompletion.EntropyMass
import OperationalCompletion.NaturalRates
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem reserved_trial_exponential_lower (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (q : Fin (m*n) → ℝ) (hq : ∀ i,0≤q i) (hqs : ∑ i,q i=1)
    (hSupport : ∀ i,0<q i → 0<hX.1.isHermitian.eigenvalues i)
    (b : ℝ) (hb : 0≤b) (hbR : b<R ∨ b=0) (hbm : b<Real.log m)
    (hH : entropy q<Real.log m+Real.log n-2*b) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (-(k:ℝ)*(divergence q hX.1.isHermitian.eigenvalues+R-b+ε)) ≤
        (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X) := by
  let d := roundedTarget b 0
  have hd : ∀ k,0<d k := roundedTarget_pos b 0
  have hdr : Tendsto (fun k : ℕ => Real.log (d k)/k) atTop (nhds b) := roundedTarget_rate_nonneg b hb
  have hdK_eventual : ∀ᶠ k : ℕ in atTop,d k≤K k := by
    rcases hbR with h | h
    · exact nat_eventually_le_of_log_rates d K hd hK b R hdr hR h
    · subst b
      apply Eventually.of_forall
      intro k
      simpa [d,roundedTarget] using Nat.succ_le_of_lt (hK k)
  have hd2 : ∀ k,0<2*d k := fun k => Nat.mul_pos (by norm_num) (hd k)
  have h2r := nat_mul_log_rate 2 (by norm_num) d hd b hdr
  have hmass := lowEntropyMass_eventual_lower hX.1.isHermitian.eigenvalues q
    hX.1.eigenvalues_nonneg hq hqs hSupport
    (fun k => reservationSafeCutoff m n k (2*d k)) _
    (reservationSafeCutoff_tendsto m n hm hn (fun k => 2*d k) hd2 b h2r) hH (ε/2) (by linarith)
  filter_upwards [hmass,nat_ratio_eventual_lower d K hd hK b R hdr hR (ε/2) (by linarith),
    hdK_eventual,
    reservationCap_eventually m n hm hn d hd b hdr hbm,grid_count_covers_local_eventually m,
    eventually_gt_atTop 0] with k hmass hratio hdK hda hcover hk
  have hdk : 0<d k := hd k
  have ha : paperReservationDivisor m n k≤m^k := by
    have hpos : 1≤m^k/paperReservationDivisor m n k := by
      change 1≤reservationLocal m n k m
      omega
    simpa only [one_mul] using
      (Nat.le_div_iff_mul_le (paperReservationDivisor_pos m n k hm hn)).mp hpos
  have hab : paperReservationDivisor m n k≤n^k := ha.trans (Nat.pow_le_pow_left hmn k)
  have hcut := reservationSafeCutoff_le_source m n k (2*d k) hm hn (hd2 k) ha hab
  have hmass' := (empiricalEntropyMass_mono hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg k hcut)
  have htest := reservedProtocol_test_width m n k (K k) (d k) hm hn hmn (hK k) hk (hd k)
    hdK hda hcover X hX
  calc
    _ = Real.exp ((k:ℝ)*(b-R-ε/2))*
        Real.exp (-(k:ℝ)*(divergence q hX.1.isHermitian.eigenvalues+ε/2)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ ((d k:ℝ)/K k)*empiricalEntropyMass hX.1.isHermitian.eigenvalues k
        (reservationSafeCutoff m n k (2*d k)) :=
      mul_le_mul hratio hmass (Real.exp_pos _).le (by positivity)
    _ ≤ ((d k:ℝ)/K k)*empiricalEntropyMass hX.1.isHermitian.eigenvalues k
        (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n) (2*d k)) :=
      mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ _ := htest

end
end OperationalCompletion
