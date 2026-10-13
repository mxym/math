import APPTReview.LacunaryMomentScalar

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- In the relevant dimensions the cap is inactive: the actual projection
rank is exactly the integer floor, not a real-valued rank surrogate. -/
theorem canonicalScaleProjection_trace {m n : ℕ} (hm : 1≤m) (hmn : m≤n)
    (d : ℝ) (hd : 0≤d) :
    (canonicalScaleProjection m n d).trace.re=(⌊(m:ℝ)^(2-d)⌋₊:ℝ) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hnR : (m:ℝ)≤n := by exact_mod_cast hmn
  have hpow : (m:ℝ)^(2-d)≤(m:ℝ)^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hmR (show (2:ℝ)-d≤2 by linarith)
    simpa only [Real.rpow_two] using h
  have hfloor : (⌊(m:ℝ)^(2-d)⌋₊:ℝ)≤(m:ℝ)^(2-d) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hD : (m:ℝ)^2≤(m:ℝ)*n := by nlinarith
  have hcap : ⌊(m:ℝ)^(2-d)⌋₊≤Fintype.card (Fin m × Fin n) := by
    have h := (hfloor.trans hpow).trans hD
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact_mod_cast h
  rw [canonicalScaleProjection,setProjection_trace,cappedRankSupport_card,Nat.min_eq_left hcap]
  rfl

/-- The floor loss in each scale contributes at most one coefficient square. -/
theorem canonical_projection_energy_lower {m n : ℕ} (hm : 1≤m) (hmn : m≤n)
    (d e : ℝ) (hd : 0≤d) (he : 0≤e) :
    e-e*(m:ℝ)^(d-2)≤
      (Real.sqrt e*(m:ℝ)^(d/2-1))^2*(canonicalScaleProjection m n d).trace.re := by
  have hmP : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  rw [canonicalScaleProjection_trace hm hmn d hd]
  have hf : (m:ℝ)^(2-d)-1≤(⌊(m:ℝ)^(2-d)⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one ((m:ℝ)^(2-d))
    linarith
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg (Real.sqrt e*(m:ℝ)^(d/2-1)))
  have hid := canonical_energy_identity (m:ℝ) d e hmP he
  have hc := canonical_coefficient_square (m:ℝ) d e hmP he
  nlinarith

noncomputable def lacunaryTraceError (ds : List ℝ) (e : ℝ → ℝ) (a M : ℝ) : ℝ :=
  a*M^(-1:ℝ)+(∑ d∈ds.toFinset,Real.sqrt (e d)*M^(-d/2))

noncomputable def lacunaryMomentError (ds : List ℝ) (e : ℝ → ℝ) (M : ℝ) : ℝ :=
  ∑ d∈ds.toFinset,e d*M^(d-2)

theorem lacunaryTraceError_nonneg (ds : List ℝ) (e : ℝ → ℝ) (a M : ℝ)
    (ha : 0≤a) (hM : 0≤M) : 0≤lacunaryTraceError ds e a M := by
  unfold lacunaryTraceError
  exact add_nonneg (mul_nonneg ha (Real.rpow_nonneg hM _))
    (Finset.sum_nonneg (fun d _ => mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hM _)))

end APPTReview
