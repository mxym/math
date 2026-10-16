import OperationalCompletion.GridGaussian
import Deviation.Reliability

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

def tailCardinalityRate (m n : ℕ) (K : ℕ → ℕ) (k : ℕ) : ℝ :=
  Real.log (4*tensorBudget m n k (K k))/k

theorem tailCardinalityRate_tendsto (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (tailCardinalityRate m n K) atTop (nhds (Real.log m+Real.log n-2*R)) := by
  have hc : Tendsto (fun k : ℕ => Real.log 4/k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := hc.add (tensorBudget_rate_limit m n hm hn K hK R hR)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with k
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hKR : (0:ℝ)<K k := by exact_mod_cast hK k
  rw [tailCardinalityRate,Real.log_mul (by norm_num) (by unfold tensorBudget; positivity)]
  ring

/-- The reverse error exponent holds uniformly over all actual PPT channels
at every sufficiently large block, including channels aware of the input. -/
theorem ppt_strict_direct_error_lower (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hlo : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R)
    (hhi : Real.log m+Real.log n-2*R<Real.log X.rank) (η : ℝ) (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop,∀ V : KrausPPTProtocol (m^k) (n^k) (K k),
      Real.exp (-(k:ℝ)*(strictDirectExponent hX.1.isHermitian.eigenvalues
        (Real.log m+Real.log n-2*R)+η)) ≤ 1-V.fidelity (tensorInput m n k X) := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  have htail := density_subset_tail_strict_direct X hX (tailCardinalityRate m n K) _
    (tailCardinalityRate_tendsto m n hm hn K hK R hR) hlo hhi (η/2) (by linarith)
  have hsmall : ∀ᶠ k : ℕ in atTop,Real.exp (-(k:ℝ)*(η/2))≤1/2 := by
    have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (show (0:ℝ)<η/2 by linarith))
    simpa only [Function.comp_apply,neg_mul] using
      (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).mono (fun _ h => h.le)
  filter_upwards [htail,hsmall,eventually_gt_atTop 0] with k htail hsmall hk
  intro V
  obtain ⟨S,hS,herr⟩ := OperationalCompletion.KrausPPTProtocol.tensor_error_tail
    m n k (K k) (hK k) V X hX (1/2)
    (by norm_num) (by norm_num)
  have hcard : (S.card:ℝ)≤Real.exp ((k:ℝ)*tailCardinalityRate m n K k) := by
    have hmR : (0:ℝ)<m := by exact_mod_cast hm
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hKR : (0:ℝ)<K k := by exact_mod_cast hK k
    have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk
    have he : (k:ℝ)*tailCardinalityRate m n K k=Real.log (4*tensorBudget m n k (K k)) := by
      unfold tailCardinalityRate
      field_simp
    rw [he,Real.exp_log (by unfold tensorBudget; positivity)]
    convert hS using 1 <;> ring
  have hp := htail S hcard
  let E := strictDirectExponent hX.1.isHermitian.eigenvalues (Real.log m+Real.log n-2*R)
  have hfactor : Real.exp (-(k:ℝ)*(E+η)) =
      Real.exp (-(k:ℝ)*(η/2))*Real.exp (-(k:ℝ)*(E+η/2)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = _ := hfactor
    _ ≤ (1/2)*Real.exp (-(k:ℝ)*(E+η/2)) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ ≤ (1/2)*(1-wordMass hX.1.isHermitian.eigenvalues k S) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by simpa only [show (1:ℝ)-1/2=1/2 by norm_num,wordMass] using herr

theorem logarithmic_rate_of_exponential_bounds (f : ℕ → ℝ) (E : ℝ)
    (hbound : ∀ η>0,∀ᶠ k : ℕ in atTop,
      Real.exp (-(k:ℝ)*(E+η))≤f k ∧ f k≤Real.exp (-(k:ℝ)*(E-η))) :
    Tendsto (fun k : ℕ => -Real.log (f k)/k) atTop (nhds E) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  apply eventually_atTop.mp
  filter_upwards [hbound (ε/2) (by linarith),eventually_gt_atTop 0] with k hk hkpos
  have hkR : (0:ℝ)<k := by exact_mod_cast hkpos
  have hf : 0<f k := (Real.exp_pos _).trans_le hk.1
  have hlo : -(k:ℝ)*(E+ε/2)≤Real.log (f k) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hk.1
  have hhi : Real.log (f k)≤-(k:ℝ)*(E-ε/2) := by
    simpa only [Real.log_exp] using Real.log_le_log hf hk.2
  have hlow : E-ε/2≤-Real.log (f k)/k := (le_div_iff₀ hkR).mpr (by nlinarith)
  have hhigh : -Real.log (f k)/k≤E+ε/2 := (div_le_iff₀ hkR).mpr (by nlinarith)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- The common grid family attains the complete strict-direct reliability
exponent for every fixed actual input, including zero eigenvalues. -/
theorem grid_reliability_limit (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hlo : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R)
    (hhi : Real.log m+Real.log n-2*R<Real.log X.rank) :
    Tendsto (fun k : ℕ => -Real.log (1-
      (gridProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X))/k)
      atTop (nhds (strictDirectExponent hX.1.isHermitian.eigenvalues
        (Real.log m+Real.log n-2*R))) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [ppt_strict_direct_error_lower m n hm hn K hK R hR X hX hlo hhi η hη,
    grid_strict_direct_error_upper m n hm hn hmn K hK R hR hRm X hX hlo hhi η hη]
      with k hlo hhi
  exact ⟨hlo _,hhi⟩

end
end OperationalCompletion
