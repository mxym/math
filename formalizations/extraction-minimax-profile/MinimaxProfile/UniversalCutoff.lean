import MinimaxProfile.UniversalFinite
import MinimaxProfile.IntegerPacking
import Spectrum.Types
import SymmetricSupport.RankAsymptotic

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport Filter
namespace MinimaxProfile
noncomputable section

/-- The factor two retains the integer quotient even near a local cap. -/
theorem cast_div_half_lower (a d : ℕ) (hd : 0 < d) (hda : d ≤ a) :
    (a:ℝ)/(2*d) ≤ ((a/d:ℕ):ℝ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hq : (1:ℝ) ≤ ((a/d:ℕ):ℝ) := by
    exact_mod_cast (Nat.one_le_div_iff hd).mpr hda
  have h := cast_div_lower a d hd
  have ha : (a:ℝ)/d ≤ 2*((a/d:ℕ):ℝ) := by linarith
  have he : (a:ℝ)/(2*d) = ((a:ℝ)/d)/2 := by ring
  rw [he]
  linarith

theorem quarter_capacity_lower (a b K : ℕ) (hK : 0 < K) (hKa : K ≤ a) (hKb : K ≤ b) :
    (a:ℝ)*b/(4*(K:ℝ)^2) ≤ (((a/K)*(b/K):ℕ):ℝ) := by
  have ha := cast_div_half_lower a K hK hKa
  have hb := cast_div_half_lower b K hK hKb
  calc
    _ = ((a:ℝ)/(2*K))*((b:ℝ)/(2*K)) := by ring
    _ ≤ ((a/K:ℕ):ℝ)*((b/K:ℕ):ℝ) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    _ = _ := by push_cast; rfl

def orbitOverhead (D k : ℕ) : ℝ :=
  ((symmetricProjector (D*D) k).rank:ℝ) * ((k:ℝ)+1)^D

theorem orbitOverhead_pos (D k : ℕ) (hD : 0 < D) : 0 < orbitOverhead D k := by
  exact mul_pos (by exact_mod_cast symmetricProjector_rank_pos (D*D) k (Nat.mul_pos hD hD))
    (pow_pos (by positivity) _)

def compressionCutoff (m n k K : ℕ) : ℝ :=
  (Real.log (((m^k:ℕ):ℝ)*((n^k:ℕ):ℝ)/(4*(K:ℝ)^2)) -
    Real.log (orbitOverhead (m*n) k)) / k

theorem compressionCutoff_identity (m n k K : ℕ) (hk : 0 < k) :
    (k:ℝ)*compressionCutoff m n k K =
      Real.log (((m^k:ℕ):ℝ)*((n^k:ℕ):ℝ)/(4*(K:ℝ)^2)) -
        Real.log (orbitOverhead (m*n) k) := by
  unfold compressionCutoff
  field_simp

/-- The numerical cutoff implies the actual natural-number rank/floor
packing budget; it is not a supplied feasibility certificate. -/
theorem compressionCutoff_budget (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk : 0 < k) (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k) :
    (ExtractionSpectrum.lowEntropyWords (ι := Fin (m*n)) k (compressionCutoff m n k K)).card *
      ((m*n)*(m*n)+k-1).choose k ≤ (m^k/K)*(n^k/K) := by
  let S := ExtractionSpectrum.lowEntropyWords (ι := Fin (m*n)) k (compressionCutoff m n k K)
  let C := (symmetricProjector ((m*n)*(m*n)) k).rank
  have hsize := ExtractionSpectrum.lowEntropyWords_card_le (ι := Fin (m*n)) k (compressionCutoff m n k K)
  have hC : 0 < C := symmetricProjector_rank_pos _ k (by positivity)
  have hO := orbitOverhead_pos (m*n) k (Nat.mul_pos hm hn)
  have hQ : (0:ℝ) < ((m^k:ℕ):ℝ)*((n^k:ℕ):ℝ)/(4*(K:ℝ)^2) := by positivity
  have he : orbitOverhead (m*n) k * Real.exp ((k:ℝ)*compressionCutoff m n k K) =
      ((m^k:ℕ):ℝ)*((n^k:ℕ):ℝ)/(4*(K:ℝ)^2) := by
    rw [compressionCutoff_identity m n k K hk, Real.exp_sub,
      Real.exp_log hQ, Real.exp_log hO]
    field_simp
  have hreal : ((S.card*C:ℕ):ℝ) ≤ (((m^k/K)*(n^k/K):ℕ):ℝ) := by
    calc
      _ ≤ orbitOverhead (m*n) k * Real.exp ((k:ℝ)*compressionCutoff m n k K) := by
        have hh := mul_le_mul_of_nonneg_right hsize (show (0:ℝ) ≤ C by positivity)
        simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          orbitOverhead, C, mul_comm, mul_left_comm, mul_assoc] using hh
      _ = _ := he
      _ ≤ _ := quarter_capacity_lower (m^k) (n^k) K hK hKa hKb
  have hnats : S.card*C ≤ (m^k/K)*(n^k/K) := by exact_mod_cast hreal
  simpa only [S,C,symmetricProjector_rank_choose] using hnats

/-- A cutoff and the original local dimensions alone produce one physical
protocol that works for every unknown density, including singular spectra. -/
theorem universal_compression_protocol (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk : 0 < k) (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1),
        ExtractionSpectrum.empiricalEntropyMass hX.1.isHermitian.eigenvalues k
          (compressionCutoff m n k K) ≤ V.fidelity (tensorInput m n k X) := by
  exact universal_set_protocol m n k K hK _ (compressionCutoff_budget m n k K hm hn hk hK hKa hKb)

end
end MinimaxProfile
