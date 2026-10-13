import APPTReview.CanonicalMoments

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def lacunaryPurityLower (ds : List ℝ) (e : ℝ → ℝ) (a M : ℝ) : ℝ :=
  (a^2+(∑ d∈ds.toFinset,e d)-lacunaryMomentError ds e M)/(1+lacunaryTraceError ds e a M)^2-
    (lacunaryTraceError ds e a M)^2

theorem lacunaryDensity_purity (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (v : Fin m × Fin n → ℂ) :
    let Y := lacunaryPerturbation m n ds e a P v
    APPT.Quantum.purity (lacunaryDensity m n ds e a P v)=
      ((m:ℝ)*n+2*Y.trace.re+(Y*Y).trace.re)/((m:ℝ)*n+Y.trace.re)^2 := by
  dsimp only
  let Y := lacunaryPerturbation m n ds e a P v
  have hB : lacunarySpike m n ds e a P v=1+Y := by
    dsimp [lacunarySpike,Y,lacunaryPerturbation]
    abel
  have ht : (1+Y).trace.re=(m:ℝ)*n+Y.trace.re := by
    simp only [Matrix.trace_add,Matrix.trace_one,Complex.add_re,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_mul,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero]
  unfold lacunaryDensity
  rw [hB,ht]
  exact normalized_identity_purity Y

theorem scalar_identity_excess_ratio (D T S : ℝ) (hD : 0<D) (hT : 0≤T) :
    D^2*((D+2*T+S)/(D+T)^2-1/D)=(S-T^2/D)/(1+T/D)^2 := by
  have hz : D+T≠0 := ne_of_gt (by linarith : 0<D+T)
  have hu : 1+T/D=(D+T)/D := by field_simp
  rw [hu,div_pow,div_div_eq_mul_div]
  have hh := normalized_perturbation_excess D 1 T S (ne_of_gt hD) (by simpa using hz)
  simp only [one_pow,mul_one] at hh
  rw [hh]
  congr 1
  field_simp

/-- Uniform-in-n finite purity lower bound for the actual canonical matrix.
Every floor error and normalization loss is retained explicitly. -/
theorem canonical_lacunary_purity_finite {m n : ℕ} (hm0 : 0<m) (hn0 : 0<n) (hmn : m≤n)
    (ds : List ℝ) (hd : ∀ d∈ds,0≤d) (e : ℝ → ℝ) (he : ∀ d∈ds,0≤e d)
    (a : ℝ) (ha : 0≤a) :
    lacunaryPurityLower ds e a m≤((m:ℝ)*n)^2*
      (APPT.Quantum.purity (canonicalLacunaryState ds e a m n hm0 hn0)-1/((m:ℝ)*n)) := by
  let v := coordinateUnitVector m n hm0 hn0
  let P := canonicalScaleProjection m n
  let Y := lacunaryPerturbation m n ds e a P v
  let D : ℝ := (m:ℝ)*n
  let T := Y.trace.re
  let S := (Y*Y).trace.re
  let E := a^2+∑ d∈ds.toFinset,e d
  let η := lacunaryMomentError ds e m
  let τ := lacunaryTraceError ds e a m
  obtain ⟨hT,hTm,hS,hE⟩ := canonical_perturbation_moments (by omega : 1≤m) hmn ds hd e he a ha v (coordinateUnitVector_norm m n hm0 hn0)
  change 0≤T at hT
  change T≤(m:ℝ)*τ at hTm
  change 0≤S at hS
  change E-η≤S at hE
  have hmP : (0:ℝ)<m := by exact_mod_cast hm0
  have hnP : (0:ℝ)<n := by exact_mod_cast hn0
  have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have hnR : (m:ℝ)≤n := by exact_mod_cast hmn
  have hD : 0<D := mul_pos hmP hnP
  have hmD : (m:ℝ)≤D := by dsimp [D]; nlinarith
  have hmD2 : (m:ℝ)^2≤D := by dsimp [D]; nlinarith
  have hτ : 0≤τ := lacunaryTraceError_nonneg ds e a (m:ℝ) ha hmP.le
  have hTr : T/D≤τ := (div_le_iff₀ hD).2 (by
    have hh := mul_le_mul_of_nonneg_right hmD hτ
    nlinarith)
  have hSq : T^2/D≤τ^2 := (div_le_iff₀ hD).2 (by
    have h1 := pow_le_pow_left₀ hT hTm 2
    have h2 := mul_le_mul_of_nonneg_right hmD2 (sq_nonneg τ)
    nlinarith)
  have hlow := scalar_normalized_moment_lower D T S E η τ hD hT hS hτ hE hTr hSq
  change lacunaryPurityLower ds e a (m:ℝ)≤D^2*(APPT.Quantum.purity (lacunaryDensity m n ds e a P v)-1/D)
  rw [lacunaryDensity_purity]
  change (E-η)/(1+τ)^2-τ^2≤D^2*((D+2*T+S)/(D+T)^2-1/D)
  rw [scalar_identity_excess_ratio D T S hD hT]
  exact hlow

end APPTReview
