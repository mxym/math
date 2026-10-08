import Entry002.Targets
import Entry002.Isolation

/-! Genuine full-lattice facts for the arbitrary planar embeddings in the target. -/
set_option autoImplicit false
open Module
namespace Entry002
variable {O : Type*} [AddCommGroup O]

/-- The actual integral coordinate map is injective. -/
theorem integralCoordinates_injective (b : Basis (Fin 2) ℤ O) :
    Function.Injective (fun x : O => fun i => b.repr x i) := by
  intro x y h
  apply b.repr.injective
  ext i
  exact congrFun h i

/-- Every allowed planar embedding preserves distinct order elements. -/
theorem planarEmbedding_injective (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : Function.Injective (planarEmbedding b e) := by
  intro x y h
  apply integralCoordinates_injective b
  funext i
  have hi := congrFun (e.injective h) i
  exact_mod_cast hi

@[simp] theorem planarEmbedding_add (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : O) :
    planarEmbedding b e (x + y) = planarEmbedding b e x + planarEmbedding b e y := by
  unfold planarEmbedding
  rw [← e.map_add]
  congr 1
  funext i
  simp

@[simp] theorem planarEmbedding_zero (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : planarEmbedding b e (0 : O) = 0 := by
  unfold planarEmbedding
  convert e.map_zero using 1
  congr 1
  funext i
  simp

/-- The image is an actual full discrete lattice: every metric ball is finite,
including after any invertible real linear change of coefficient coordinates. -/
theorem planarEmbedding_finite_balls (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (T : ℝ) :
    {x : O | ‖planarEmbedding b e x‖ ≤ T}.Finite := by
  let ec : CoeffSpace ≃L[ℝ] Plane := e.toContinuousLinearEquiv
  have hf := coefficient_lattice_finite_balls ec T
  exact hf.preimage (integralCoordinates_injective b).injOn

end Entry002
