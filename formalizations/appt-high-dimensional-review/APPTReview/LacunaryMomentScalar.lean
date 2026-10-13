import APPTReview.PositiveMoments

open scoped BigOperators Topology
open Matrix Filter
namespace APPTReview

/-- Squaring a canonical coefficient retains its exact finite power. -/
theorem canonical_coefficient_square (M d e : ℝ) (hM : 0<M) (he : 0≤e) :
    (Real.sqrt e*M^(d/2-1))^2=e*M^(d-2) := by
  rw [mul_pow,Real.sq_sqrt he]
  have hp : (M^(d/2-1))^2=M^(d-2) := by
    rw [pow_two,← Real.rpow_add hM]
    congr 1
    ring
  rw [hp]

theorem canonical_energy_identity (M d e : ℝ) (hM : 0<M) (he : 0≤e) :
    (Real.sqrt e*M^(d/2-1))^2*M^(2-d)=e := by
  rw [canonical_coefficient_square M d e hM he,mul_assoc,← Real.rpow_add hM]
  have h0 : d-2+(2-d)=0 := by ring
  rw [h0,Real.rpow_zero,mul_one]

theorem canonical_trace_identity (M d e : ℝ) (hM : 0<M) :
    (Real.sqrt e*M^(d/2-1))*M^(2-d)=M*(Real.sqrt e*M^(-d/2)) := by
  rw [mul_assoc,← Real.rpow_add hM]
  have hp : M*M^(-d/2)=M^(d/2-1+(2-d)) := by
    calc
      M*M^(-d/2)=M^(1:ℝ)*M^(-d/2) := by rw [Real.rpow_one]
      _ = M^((1:ℝ)+(-d/2)) := (Real.rpow_add hM _ _).symm
      _ = _ := by congr 1; ring
  calc
    Real.sqrt e*M^(d/2-1+(2-d))=Real.sqrt e*(M*M^(-d/2)) := by rw [hp]
    _ = _ := by ring

/-- A denominator-safe lower estimate; the actual second moment is nonnegative,
so this remains valid even when the lower energy estimate is temporarily negative. -/
theorem scalar_normalized_moment_lower (D T S E η τ : ℝ)
    (hD : 0<D) (hT : 0≤T) (hS : 0≤S) (hτ : 0≤τ)
    (hE : E-η≤S) (hTr : T/D≤τ) (hSq : T^2/D≤τ^2) :
    (E-η)/(1+τ)^2-τ^2≤(S-T^2/D)/(1+T/D)^2 := by
  have hu : 0<1+T/D := by positivity
  have hv : 0<1+τ := by positivity
  have huv : (1+T/D)^2≤(1+τ)^2 := pow_le_pow_left₀ hu.le (by linarith) 2
  have hfirst : (E-η)/(1+τ)^2≤S/(1+T/D)^2 := by
    exact (div_le_div_of_nonneg_right hE (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left hS (sq_pos_of_pos hu) huv)
  have hsecond : (T^2/D)/(1+T/D)^2≤τ^2 := by
    have h1 : 1≤(1+T/D)^2 := by have ht:=div_nonneg hT hD.le; nlinarith
    have hnon : 0≤T^2/D := div_nonneg (sq_nonneg _) hD.le
    have hh := div_le_div_of_nonneg_left hnon (by norm_num : (0:ℝ)<1) h1
    simp only [div_one] at hh
    exact hh.trans hSq
  simp only [sub_div] at hfirst ⊢
  linarith

end APPTReview
