import APPTReview.CanonicalLacunaryState

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The finite spike-coupling error cannot be silently set to zero. -/
theorem spike_finite_error_cannot_be_deleted :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i=j then 0 else 1/4
    realRayleigh A (fun _ => 1)+2*(1:ℝ)*1*1>
      max (1/4:ℝ) 1*(∑ _i : Fin 2,(1:ℝ)^2) := by
  norm_num [realRayleigh,Fintype.sum_prod_type,Fin.sum_univ_two]

/-- One negative slot yields two symmetric ordered weights, not one. -/
theorem symmetric_rank_mass_factor_two :
    let q : Fin 2 × Fin 2 → ℝ := fun p => if p=(1,0) then 1 else 0
    (∑ p,symmetricCompressionWeight q p)=2 ∧ (∑ p,q p)=1 := by
  norm_num [symmetricCompressionWeight,negativeCompressionWeight,
    Fintype.sum_prod_type,Fin.sum_univ_two]

/-- Correct zero-vector behavior of the homogeneous matrix-plus-spike test. -/
theorem zero_spike_rayleigh {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (a : ℝ) (i j : ι) :
    realRayleigh A (fun _ => 0)+2*a*(0:ℝ)*0=0 := by simp [realRayleigh]

/-- A fully instantiated nonempty hierarchy with positive energies and spike.
The endpoint concerns actual integer-projection density matrices, not a graph interface. -/
theorem two_scale_physical_family :
    ∃ M : ℕ, 2≤M ∧ ∀ (m n : ℕ) (hm : 0<m) (hn : 0<n), M≤m → m≤n →
      APPT.Quantum.IsDensity (canonicalLacunaryState [1/3,1/9] (fun _ => 1/8) 1 m n hm hn) ∧
      APPT.Quantum.AbsolutelyPPT (canonicalLacunaryState [1/3,1/9] (fun _ => 1/8) 1 m n hm hn) := by
  apply canonical_lacunary_states_appt [1/3,1/9] (by norm_num [LacunaryScales])
    (by intro d hd; simp only [List.mem_cons,List.not_mem_nil,or_false] at hd; rcases hd with rfl|rfl <;> norm_num)
    (fun _ => 1/8) (1/8) 1 (by norm_num)
    (by intros; norm_num) (by intros; norm_num) (by norm_num) (by norm_num)
  norm_num [scaleEnergyBound,show Real.sqrt (4:ℝ)=2 from by nlinarith [Real.sq_sqrt (show (0:ℝ)≤4 by norm_num),Real.sqrt_nonneg (4:ℝ)]]

end APPTReview
