import GaussianGramIsometry
import GaussianRegularStationarity

/-! Regular first moments are independent of the Gram realization.
The proof transfers the actual envelope derivatives under an isometric
embedding, rather than assuming an embedding law for Gaussian moments. -/
open Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem balancedMoment_regular_gram
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i = 0) (hg : scoreGram v = regularCovariance (d+2)) :
    ∀ i,balancedMoment v i = simplexConstant (d+2) • v i := by
  classical
  have hk : 2 ≤ d+2 := by omega
  obtain ⟨T,hT⟩ := centered_gram_linearIsometry v (regularRows (d+2)) hv hz
    regularRows_sum hg
  have hdirections (h : Fin (d+2) → Space (d+1)) :
      (∑ i,⟪h i,balancedMoment v i⟫) =
        simplexConstant (d+2) * ∑ i,⟪h i,v i⟫ := by
    let p : ℝ → Fin (d+2) → Space (d+1) := fun t i => v i+t•h i
    let q : ℝ → Fin (d+2) → Space (d+2) :=
      fun t i => regularRows (d+2) i+t•T (h i)
    have hp : HasDerivAt p h 0 := by
      convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const h) using 1
      · rfl
      · simp
    have hq : HasDerivAt q (fun i => T (h i)) 0 := by
      convert (hasDerivAt_const (0:ℝ) (regularRows (d+2))).add
        ((hasDerivAt_id (0:ℝ)).smul_const (fun i => T (h i))) using 1
      · rfl
      · simp
    have he : (fun t => equalMassValue (p t)) = (fun t => equalMassValue (q t)) := by
      funext t
      apply equalMassValue_eq_of_gram_eq
      ext i j
      change ⟪p t i,p t j⟫ = ⟪q t i,q t j⟫
      have hmap (i : Fin (d+2)) : T (p t i) = q t i := by
        simp only [p,q,map_add,map_smul,hT]
      rw [← hmap i,← hmap j,T.inner_map_map]
    have hp0 : p 0 = v := by funext i; simp [p]
    have hq0 : q 0 = regularRows (d+2) := by funext i; simp [q]
    have ha := equalMassValue_path_derivative p 0 h
      (by rw [hp0]; exact hv.injective) hp
    have hb := equalMassValue_path_derivative q 0 (fun i => T (h i))
      (by rw [hq0]; exact regularRows_injective hk) hq
    rw [he] at ha
    have hu := ha.unique hb
    rw [hp0,hq0] at hu
    simp_rw [balancedMoment_regular hk,real_inner_smul_right,← hT,
      T.inner_map_map,← Finset.mul_sum] at hu
    exact hu
  intro i
  apply ext_inner_left ℝ
  intro x
  have he := hdirections (fun j => if j = i then x else 0)
  have hsum (g : Fin (d+2) → Space (d+1)) :
      (∑ j,⟪if j=i then x else 0,g j⟫) = ⟪x,g i⟫ := by
    calc
      _ = ∑ j,if j=i then ⟪x,g i⟫ else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j=i <;> simp [hj]
      _ = _ := by simp
  rw [hsum,hsum] at he
  simpa only [real_inner_smul_right] using he

end GaussianMeasureBridge
