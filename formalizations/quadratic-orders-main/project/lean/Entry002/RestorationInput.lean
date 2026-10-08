import Entry002.Sieve
import Entry002.Embedding
import Entry002.ExceptionalGraphs

/-! The enlarged-exception graph bound from the bounded-norm isolation radius.
The exception set itself is allowed to be infinite. The actual product-norm
integrality premise is explicit; identifying it for a number field is separate.
-/
set_option autoImplicit false
open Module
namespace Entry002
variable {L : Type*} [AddCommGroup L]

/-- Close bounded-norm pairs imply a uniform finite component bound on the
actual exceptional graph, even with infinitely many exceptional vertices. -/
theorem exceptional_component_bound_real
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (E : Set L)
    (hintegral : ∀ x y : L, x ≠ y → ∃ n : ℤ,
      (planarEmbedding b e y 0 - planarEmbedding b e x 0) *
      (planarEmbedding b e y 1 - planarEmbedding b e x 1) = (n : ℝ) ∧ n ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M)
    (hE : ∀ x ∈ E, |planarEmbedding b e x 0 * planarEmbedding b e x 1| ≤ M) :
    ∃ B : ℕ, UniformComponentBound (latticeGraph b e R E) B := by
  have hpairs := finite_real_minkowski_close_pairs (planarEmbedding b e)
    (planarEmbedding_finite_balls b e) hintegral (R := R) hM
  have hf := (hpairs.image Prod.fst).preimage
    (show Function.Injective (fun x : E => (x : L)) from Subtype.val_injective).injOn
  have hnon : (nonisolatedVertices (latticeGraph b e R E)).Finite := by
    apply hf.subset
    rintro x ⟨y, hxy⟩
    refine ⟨(x.val, y.val), ?_, rfl⟩
    exact ⟨(fun he => hxy.1 (Subtype.ext he)), hE x x.property, hE y y.property,
      by simpa only [norm_sub_rev] using hxy.2⟩
  exact ⟨_, uniformComponentBound_of_finite_nonisolated _ hnon⟩

end Entry002
