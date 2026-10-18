import OperationalCompletion.CappedHolder

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem log_min_one (x : ℝ) (hx : 0<x) : Real.log (min 1 x)=min 0 (Real.log x) := by
  rcases le_total 1 x with h | h
  · rw [min_eq_left h,Real.log_one,min_eq_left (Real.log_nonneg h)]
  · rw [min_eq_right h,min_eq_right (Real.log_nonpos hx.le h)]

theorem min_zero_div (x k : ℝ) (hk : 0<k) : min 0 x/k=min 0 (x/k) := by
  rcases le_total 0 x with h | h
  · rw [min_eq_left h,zero_div,min_eq_left (div_nonneg h hk.le)]
  · rw [min_eq_right h,min_eq_right (div_nonpos_of_nonpos_of_nonneg h hk.le)]

theorem localBeta_log_identity (m k K : ℕ) (hm : 0<m) (hk : 0<k) (hK : 0<K) :
    Real.log (localBeta m k K)/k=min 0 (Real.log m-Real.log K/k) := by
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hKR : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  rw [localBeta,log_min_one _ (div_pos (pow_pos hmR k) hKR),min_zero_div _ _ hkR,
    Real.log_div (by positivity) (ne_of_gt hKR),Real.log_pow,sub_div]
  congr 2
  field_simp

theorem localBeta_log_rate (m : ℕ) (hm : 0<m) (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k : ℕ => Real.log (localBeta m k (K k))/k) atTop
      (nhds (-max 0 (R-Real.log m))) := by
  have h := (tendsto_const_nhds (x := (0:ℝ))).min ((tendsto_const_nhds (x := Real.log m)).sub hR)
  have he : min 0 (Real.log m-R)=-max 0 (R-Real.log m) := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (localBeta_log_identity m k (K k) hm hk (hK k)).symm

def normalizedBudget (m n k K : ℕ) : ℝ := tensorBudget m n k K/(localBeta m k K)^2

theorem normalizedBudget_pos (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hK : 0<K) :
    0<normalizedBudget m n k K := by
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hKR : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hb := localBeta_pos m k K hm hK
  unfold normalizedBudget tensorBudget
  positivity

theorem normalizedBudget_rate (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k : ℕ => Real.log (normalizedBudget m n k (K k))/k) atTop
      (nhds (cappedEntropyRate m n R)) := by
  have h := (tensorBudget_rate_limit m n hm hn K hK R hR).sub
    ((localBeta_log_rate m hm K hK R hR).const_mul 2)
  have he : Real.log m+Real.log n-2*R-2*(-max 0 (R-Real.log m))=cappedEntropyRate m n R := by
    unfold cappedEntropyRate
    simp only [min_def,max_def]
    split_ifs <;> linarith
  rw [he] at h
  apply h.congr'
  filter_upwards with k
  have hb := localBeta_pos m k (K k) hm (hK k)
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hKR : (0:ℝ)<K k := Nat.cast_pos.mpr (hK k)
  rw [normalizedBudget,Real.log_div (by unfold tensorBudget; positivity) (by positivity),Real.log_pow]
  ring

theorem positive_sequence_exponential_upper (β : ℕ → ℝ) (hβ : ∀ k,0<β k)
    (B : ℝ) (hB : Tendsto (fun k : ℕ => Real.log (β k)/k) atTop (nhds (-B)))
    (η : ℝ) (hη : 0<η) : ∀ᶠ k : ℕ in atTop,β k≤Real.exp (-(k:ℝ)*(B-η)) := by
  filter_upwards [hB.eventually_lt_const (show -B< -B+η by linarith),eventually_gt_atTop 0]
    with k hk hkpos
  have hh := (div_lt_iff₀ (Nat.cast_pos.mpr hkpos)).mp hk
  have he : Real.log (β k)≤-(k:ℝ)*(B-η) := by nlinarith
  exact (Real.exp_log (hβ k)).symm.trans_le (Real.exp_le_exp.mpr he)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem capped_variational_eventually_exponential (p : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (F β r : ℕ → ℝ) (hβ : ∀ k,0<β k) (hr : ∀ k,0<r k)
    (hcap : ∀ k,F k≤β k)
    (hu : ∀ α : ℝ,1<α → α≤2 → ∀ k,
      F k≤β k*((partition p α)^k)^(1/α)*(r k)^((α-1)/α))
    (B c : ℝ) (hB : Tendsto (fun k : ℕ => Real.log (β k)/k) atTop (nhds (-B)))
    (hc : Tendsto (fun k : ℕ => Real.log (r k)/k) atTop (nhds c))
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop,F k≤Real.exp (-(k:ℝ)*
      (B+(⨅ q : ProbabilityVector (PositiveSupport p),primalObjective (supportLaw p) c q.1)-η)) := by
  have hnorm := holder_variational_eventually_exponential p hp hs (fun k => F k/β k) r hr
    (fun k => (div_le_one (hβ k)).mpr (hcap k))
    (fun α hα hα2 k => (div_le_iff₀ (hβ k)).mpr (by
      convert hu α hα hα2 k using 1 <;> ring)) c hc (η/2) (by linarith)
  filter_upwards [hnorm,positive_sequence_exponential_upper β hβ B hB (η/2) (by linarith)]
    with k hnorm hbeta
  calc
    F k = β k*(F k/β k) := by field_simp [ne_of_gt (hβ k)]
    _ ≤ β k*Real.exp (-(k:ℝ)*((⨅ q : ProbabilityVector (PositiveSupport p),
          primalObjective (supportLaw p) c q.1)-η/2)) :=
      mul_le_mul_of_nonneg_left hnorm (hβ k).le
    _ ≤ Real.exp (-(k:ℝ)*(B-η/2))*
        Real.exp (-(k:ℝ)*((⨅ q : ProbabilityVector (PositiveSupport p),
          primalObjective (supportLaw p) c q.1)-η/2)) :=
      mul_le_mul_of_nonneg_right hbeta (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end
end OperationalCompletion
