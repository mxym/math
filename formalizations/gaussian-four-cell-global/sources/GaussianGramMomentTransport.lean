import GaussianGramIsometry
import GaussianActualEnvelope
import GaussianWinningMomentSpan

/-! Transport of genuine optimized Gaussian moments under Gram embeddings.
Envelope derivatives determine the score-span component; reflection proves
that there is no component in the orthogonal complement. -/
open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d e : ℕ}

theorem balancedMoment_gram_embedding
    (v : Fin (d+2) → Space (d+1)) (u : Fin (d+2) → Space e)
    (hv : AffineIndependent ℝ v) (hzv : ∑ i,v i = 0) (hzu : ∑ i,u i = 0)
    (hg : scoreGram v = scoreGram u) :
    ∃ T : Space (d+1) →ₗᵢ[ℝ] Space e,
      (∀ i,T (v i) = u i) ∧ (∀ i,T (balancedMoment v i) = balancedMoment u i) := by
  classical
  obtain ⟨T,hT⟩ := centered_gram_linearIsometry v u hv hzv hzu hg
  have hu : Function.Injective u := by
    intro i j he
    apply hv.injective
    apply T.injective
    simpa only [hT] using he
  have hdir (h : Fin (d+2) → Space (d+1)) :
      (∑ i,⟪h i,balancedMoment v i⟫) = ∑ i,⟪T (h i),balancedMoment u i⟫ := by
    let p : ℝ → Fin (d+2) → Space (d+1) := fun t i => v i+t•h i
    let q : ℝ → Fin (d+2) → Space e := fun t i => u i+t•T (h i)
    have hp : HasDerivAt p h 0 := by
      convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const h) using 1
      · rfl
      · simp
    have hq : HasDerivAt q (fun i => T (h i)) 0 := by
      convert (hasDerivAt_const (0:ℝ) u).add
        ((hasDerivAt_id (0:ℝ)).smul_const (fun i => T (h i))) using 1
      · rfl
      · simp
    have he : (fun t => equalMassValue (p t)) = (fun t => equalMassValue (q t)) := by
      funext t
      apply equalMassValue_eq_of_gram_eq
      ext i j
      change ⟪p t i,p t j⟫ = ⟪q t i,q t j⟫
      have hmap (i : Fin (d+2)) : T (p t i) = q t i := by simp [p,q,hT]
      rw [← hmap i,← hmap j,T.inner_map_map]
    have hp0 : p 0 = v := by funext i; simp [p]
    have hq0 : q 0 = u := by funext i; simp [q]
    have ha := equalMassValue_path_derivative p 0 h (by rw [hp0]; exact hv.injective) hp
    have hb := equalMassValue_path_derivative q 0 (fun i => T (h i)) (by rw [hq0]; exact hu) hq
    rw [he] at ha
    simpa only [hp0,hq0] using ha.unique hb
  have hinner (i : Fin (d+2)) (x : Space (d+1)) :
      ⟪x,balancedMoment v i⟫ = ⟪T x,balancedMoment u i⟫ := by
    have he := hdir (fun j => if j=i then x else 0)
    have hl (g : Fin (d+2) → Space (d+1)) :
        (∑ j,⟪if j=i then x else 0,g j⟫) = ⟪x,g i⟫ := by
      calc
        _ = ∑ j,if j=i then ⟪x,g i⟫ else 0 := by
          apply Finset.sum_congr rfl; intro j _; by_cases hj : j=i <;> simp [hj]
        _ = _ := by simp
    have hr (g : Fin (d+2) → Space e) :
        (∑ j,⟪T (if j=i then x else 0),g j⟫) = ⟪T x,g i⟫ := by
      calc
        _ = ∑ j,if j=i then ⟪T x,g i⟫ else 0 := by
          apply Finset.sum_congr rfl; intro j _; by_cases hj : j=i <;> simp [hj]
        _ = _ := by simp
    simpa only [hl,hr] using he
  refine ⟨T,hT,fun i => ?_⟩
  have hspan : Submodule.span ℝ (range u) ≤ T.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro y ⟨j,rfl⟩
    exact ⟨v j,hT j⟩
  have hb : balancedMoment u i ∈ T.toLinearMap.range :=
    hspan (balancedMoment_mem_score_span u i)
  have ha : T (balancedMoment v i) ∈ T.toLinearMap.range := ⟨balancedMoment v i,rfl⟩
  obtain ⟨x,hx⟩ := T.toLinearMap.range.sub_mem hb ha
  have hz : ⟪balancedMoment u i-T (balancedMoment v i),
      balancedMoment u i-T (balancedMoment v i)⟫ = 0 := by
    conv_lhs => lhs; rw [← hx]
    rw [inner_sub_right]
    change ⟪T x,balancedMoment u i⟫-⟪T x,T (balancedMoment v i)⟫ = 0
    rw [T.inner_map_map,← hinner i x,sub_self]
  exact (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hz)).symm

end GaussianMeasureBridge
