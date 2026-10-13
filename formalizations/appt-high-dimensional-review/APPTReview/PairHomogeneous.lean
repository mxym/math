import APPTReview.LacunarySpikeLimit

open scoped BigOperators
open Matrix
namespace APPTReview

/-- Homogenize the pair-spike bound, including the zero vector. -/
theorem pair_rayleigh_homogeneous {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a C : ℝ) (i j : ι)
    (hunit : ∀ s : ι → ℝ,(∀ k,0≤s k) → (∑ k,(s k)^2)=1 →
      realRayleigh A s+2*a*s i*s j≤C)
    (s : ι → ℝ) (hs : ∀ k,0≤s k) :
    realRayleigh A s+2*a*s i*s j≤C*∑ k,(s k)^2 := by
  let q := ∑ k,(s k)^2
  have hq : 0≤q := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  by_cases hq0 : q=0
  · have hz (k) : s k=0 := by
      have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => sq_nonneg (s l)) (Finset.mem_univ k)
      change (s k)^2≤q at hh
      rw [hq0] at hh
      nlinarith
    simp [realRayleigh,hz]
  · let r := Real.sqrt q
    have hr : 0<r := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm hq0))
    have hr2 : r^2=q := Real.sq_sqrt hq
    let y : ι → ℝ := fun k => s k/r
    have hy (k) : 0≤y k := div_nonneg (hs k) hr.le
    have hyn : (∑ k,(y k)^2)=1 := by
      simp only [y,div_pow]
      rw [← Finset.sum_div,hr2]
      exact div_self hq0
    have he : q*realRayleigh A y=realRayleigh A s := by
      unfold realRayleigh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      dsimp [y]
      rw [div_mul_div_comm,← pow_two,hr2]
      field_simp
    have hp : q*(2*a*y i*y j)=2*a*s i*s j := by
      have hh : y i*y j=s i*s j/q := by dsimp [y]; rw [div_mul_div_comm,← pow_two,hr2]
      calc
        q*(2*a*y i*y j)=2*a*(q*(y i*y j)) := by ring
        _ = _ := by rw [hh]; field_simp
    have hh := mul_le_mul_of_nonneg_left (hunit y hy hyn) hq
    rw [mul_add,he,hp] at hh
    simpa only [q,mul_comm] using hh

/-- A single threshold covers all unnormalized nonnegative Schmidt vectors. -/
theorem lacunary_single_spike_bound (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (a ε : ℝ) (ha : 0≤a) (hε : 0<ε) :
    ∃ M : ℕ, ∀ m : ℕ, M≤m →
      ∀ w : ℝ → Fin m × Fin m → ℝ,
      (∀ d∈ds,∀ z,0≤w d z) → (∀ d∈ds,∀ z,w d z≤1) →
      (∀ d∈ds,(∑ z,w d z)≤2*(m:ℝ)^(2-d)) →
      ∀ s : Fin m → ℝ, (∀ i,0≤s i) → ∀ i j : Fin m, i≠j →
      realRayleigh (lacunarySparseMatrix m ds e w) s+2*a*s i*s j≤
        (max (scaleEnergyBound ds e B) a+ε)*(∑ k,(s k)^2) := by
  obtain ⟨M,hM⟩ := lacunary_single_spike_unit_bound ds hds hd1 e B hB he heB a ε ha hε
  refine ⟨M,?_⟩
  intro m hm w hw hw1 hwr s hs i j hij
  exact pair_rayleigh_homogeneous _ a _ i j
    (fun t ht ht1 => hM m hm w hw hw1 hwr t ht ht1 i j hij) s hs

end APPTReview
