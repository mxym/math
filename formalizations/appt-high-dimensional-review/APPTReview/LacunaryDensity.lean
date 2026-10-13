import APPTReview.LacunarySufficiency

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def lacunaryDensity (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (v : Fin m × Fin n → ℂ) :=
  (1/(lacunarySpike m n ds e a P v).trace.re) • lacunarySpike m n ds e a P v

/-- The isotropic identity makes the normalizing trace strictly positive in
nonzero dimensions. No totalized division convention supplies a density matrix. -/
theorem lacunarySpike_retrace_lower (m n : ℕ) (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (ha : 0≤a) (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (v : Fin m × Fin n → ℂ) :
    (m:ℝ)*n≤(lacunarySpike m n ds e a P v).trace.re := by
  have hsum : 0≤∑ d∈ds.toFinset,(Real.sqrt (e d)*(m:ℝ)^(d/2-1))*(P d).trace.re := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
      (RCLike.nonneg_iff.mp (hP d (List.mem_toFinset.mp hd)).trace_nonneg).1
  have hpure : 0≤(Matrix.vecMulVec v (star v)).trace.re :=
    (RCLike.nonneg_iff.mp (Matrix.posSemidef_vecMulVec_self_star v).trace_nonneg).1
  have hp := mul_nonneg ha hpure
  simp only [lacunarySpike,Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,Matrix.trace_one,
    Complex.add_re,Complex.re_sum,Complex.smul_re,Complex.natCast_re,smul_eq_mul,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero]
  linarith

theorem lacunaryDensity_isDensity {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ) (ha : 0≤a)
    (P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hP : ∀ d∈ds,(P d).PosSemidef) (v : Fin m × Fin n → ℂ) :
    APPT.Quantum.IsDensity (lacunaryDensity m n ds e a P v) := by
  let A := lacunarySpike m n ds e a P v
  have hA : A.PosSemidef := lacunarySpike_posSemidef m n ds e a ha P hP v
  have hdim : (0:ℝ)<(m:ℝ)*n := by exact_mod_cast Nat.mul_pos hm hn
  have ht : 0<A.trace.re := hdim.trans_le (lacunarySpike_retrace_lower m n ds e a ha P hP v)
  have hreal : A.trace=(A.trace.re:ℂ) := by
    apply Complex.ext
    · rfl
    · have hi := (RCLike.nonneg_iff.mp hA.trace_nonneg).2
      change A.trace.im=0 at hi
      simpa only [Complex.ofReal_im] using hi
  refine ⟨hA.smul (by positivity : (0:ℝ)≤1/A.trace.re),?_⟩
  change ((1/A.trace.re:ℝ) • A).trace=1
  rw [Matrix.trace_smul,Complex.real_smul,hreal]
  simp only [Complex.ofReal_re,← Complex.ofReal_mul]
  simp [ne_of_gt ht]

/-- Actual normalized multiscale APPT states, uniformly in the larger dimension
and all positive contractions satisfying the physical trace budgets. -/
theorem lacunary_density_eventually (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B a : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ha : 0≤a) (ha2 : a<2) (henergy : scaleEnergyBound ds e B<2) :
    ∃ M : ℕ, 2≤M ∧ ∀ m n : ℕ, M≤m → m≤n →
      ∀ P : ℝ → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      (∀ d∈ds,(P d).PosSemidef) → (∀ d∈ds,(1-P d).PosSemidef) →
      (∀ d∈ds,(P d).trace.re≤(m:ℝ)^(2-d)) →
      ∀ v : Fin m × Fin n → ℂ, star v ⬝ᵥ v=1 →
      APPT.Quantum.IsDensity (lacunaryDensity m n ds e a P v) ∧
      APPT.Quantum.AbsolutelyPPT (lacunaryDensity m n ds e a P v) := by
  obtain ⟨M,hM2,hM⟩ := lacunarySpike_absolutelyPPT_eventually ds hds hd1 e B a hB he heB ha ha2 henergy
  refine ⟨M,hM2,?_⟩
  intro m n hm hmn P hP hI htr v hv
  have hm0 : 0<m := by omega
  have hn0 : 0<n := by omega
  refine ⟨lacunaryDensity_isDensity hm0 hn0 ds e a ha P hP v,?_⟩
  apply APPT.Quantum.absolutelyPPT_smul (hM m hm n P hP hI htr v hv)
  have ht := lacunarySpike_retrace_lower m n ds e a ha P hP v
  have hdim : (0:ℝ)<(m:ℝ)*n := by exact_mod_cast Nat.mul_pos hm0 hn0
  exact le_of_lt (one_div_pos.mpr (hdim.trans_le ht))

end APPTReview
