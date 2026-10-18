import OperationalCompletion.ReservationLimit
import OperationalCompletion.GridCoverage

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

def reservationLoss (m n k : ℕ) : ℝ := Real.log (4*(paperReservationDivisor m n k:ℝ)^2)
def reservationSafeCutoff (m n k K : ℕ) : ℝ := compressionCutoff m n k K-reservationLoss m n k/k

theorem reservationLoss_expansion (m n k : ℕ) (hm : 0<m) (hn : 0<n) :
    reservationLoss m n k=Real.log 4+2*Real.log (paperReservationDivisor m n k:ℝ) := by
  have hQ : (0:ℝ)<paperReservationDivisor m n k := Nat.cast_pos.mpr (paperReservationDivisor_pos m n k hm hn)
  unfold reservationLoss
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  norm_num

theorem reservationLoss_div_sqrt (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    Tendsto (fun k : ℕ => reservationLoss m n k/Real.sqrt k) atTop (nhds 0) := by
  have hc : Tendsto (fun k : ℕ => Real.log 4/Real.sqrt k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [reservationLoss_expansion m n _ hm hn,add_div,mul_div_assoc,mul_zero,add_zero]
    using hc.add ((paperReservationDivisor_log_div_sqrt m n hm hn).const_mul 2)

theorem reservationLoss_div_nat (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    Tendsto (fun k : ℕ => reservationLoss m n k/k) atTop (nhds 0) :=
  div_nat_zero_of_div_sqrt_zero _ (reservationLoss_div_sqrt m n hm hn)

theorem reservationSafeCutoff_le_source (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hK : 0<K)
    (ha : paperReservationDivisor m n k≤m^k) (hb : paperReservationDivisor m n k≤n^k) :
    reservationSafeCutoff m n k K≤sourceCutoff (m*n) k
      (reservationLocal m n k m) (reservationLocal m n k n) K :=
  sourceCutoff_div_lower (m*n) k (m^k) (n^k) K (paperReservationDivisor m n k)
    hK (paperReservationDivisor_pos m n k hm hn) ha hb

theorem reservedProtocol_prefix (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hK : 0<K) (hk : 0<k) (ha : 0<reservationLocal m n k m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (j : ℕ) (hj : j<gridSectorCount k) :
    ((gridWidth K (reservationLocal m n k m) j:ℝ)/K)*
      empiricalEntropyMass hX.1.isHermitian.eigenvalues k
        (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n)
          (gridWidth K (reservationLocal m n k m) j))≤
            (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) :=
  (reservedProtocol_guarantees m n k K hm hn hmn hK hk ha).1 X hX j hj

theorem reservedProtocol_first_mass (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hK : 0<K) (hk : 0<k) (hKa : K≤reservationLocal m n k m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    empiricalEntropyMass hX.1.isHermitian.eigenvalues k
      (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n) K)≤
        (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have h := reservedProtocol_prefix m n k K hm hn hmn hK hk (hK.trans_le hKa) X hX 0
    (gridSectorCount_pos k)
  have he : gridWidth K (reservationLocal m n k m) 0=K := by
    simp only [gridWidth,pow_zero,Nat.div_one,min_eq_left hKa]
    exact max_eq_right (by omega)
  have hKR : (K:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hK)
  simpa only [he,div_self hKR,one_mul] using h

theorem reservedProtocol_safe_mass (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hK : 0<K) (hk : 0<k) (hKa : K≤reservationLocal m n k m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    empiricalEntropyMass hX.1.isHermitian.eigenvalues k (reservationSafeCutoff m n k K)≤
      (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have ha : paperReservationDivisor m n k≤m^k := by
    have hpositive : 1≤m^k/paperReservationDivisor m n k := by
      change 1≤reservationLocal m n k m
      omega
    simpa only [one_mul] using
      (Nat.le_div_iff_mul_le (paperReservationDivisor_pos m n k hm hn)).mp hpositive
  have hb := ha.trans (Nat.pow_le_pow_left hmn k)
  exact (empiricalEntropyMass_mono _ hX.1.eigenvalues_nonneg k
    (reservationSafeCutoff_le_source m n k K hm hn hK ha hb)).trans
    (reservedProtocol_first_mass m n k K hm hn hmn hK hk hKa X hX)

theorem reservationSafeCutoff_tendsto (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k => reservationSafeCutoff m n k (K k)) atTop
      (nhds (Real.log m+Real.log n-2*R)) := by
  simpa only [reservationSafeCutoff,sub_zero] using
    (compressionCutoff_tendsto m n hm hn K hK R hR).sub (reservationLoss_div_nat m n hm hn)

theorem reservationSafeCutoff_gaussian (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (H z : ℝ)
    (hsecond : Tendsto (fun k : ℕ =>
      (Real.log (K k)-k*((Real.log m+Real.log n-H)/2))/Real.sqrt k) atTop (nhds z)) :
    Tendsto (fun k : ℕ => (k*reservationSafeCutoff m n k (K k)-k*H)/Real.sqrt k)
      atTop (nhds (-2*z)) := by
  have h := (compressionCutoff_gaussian m n hm hn K hK H z hsecond).sub
    (reservationLoss_div_sqrt m n hm hn)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  unfold reservationSafeCutoff
  have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  <;> ring

end
end OperationalCompletion
