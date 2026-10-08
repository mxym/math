import Entry002.Restoration
import Entry002.ExceptionalGraphs
import Entry002.Sieve
import Entry002.Embedding
import Entry002.ComplexIsolation

/-!
# Restoration from a finite principal sieve in every quadratic order

This proves the Section 9 passage from a genuine bounded-component avoiding
graph to the graph of all irreducibles. The finite-sieve input is explicit;
this file does not claim the analytic sieve theorem or `MainTarget`.
-/

namespace Entry002

open Module

/-- An injective graph homomorphism transfers a uniform component bound. -/
theorem componentBound_of_injective_hom {V W : Type*}
    (G : SimpleGraph V) (F : SimpleGraph W) (φ : G →g F)
    (hinj : Function.Injective φ) {B : ℕ} (hB : UniformComponentBound F B) :
    UniformComponentBound G B := by
  intro x
  have hmap : ∀ y ∈ componentVertices G x, φ y ∈ componentVertices F (φ x) := by
    rintro y ⟨p⟩
    exact (p.map φ).reachable
  have hfinite := ((hB (φ x)).1.preimage hinj.injOn).subset hmap
  exact ⟨hfinite, (Set.ncard_le_ncard_of_injOn φ hmap hinj.injOn
    (hB (φ x)).1).trans (hB (φ x)).2⟩

variable {O : Type*} [CommRing O]

@[simp] theorem planarEmbedding_sub (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : O) :
    planarEmbedding b e (x - y) = planarEmbedding b e x - planarEmbedding b e y := by
  unfold planarEmbedding
  calc
    _ = e ((fun i => (b.repr x i : ℝ)) - (fun i => (b.repr y i : ℝ))) := by
      congr 1
      funext i
      simp
    _ = _ := e.map_sub _ _

/-- Finite lattice balls bound every degree of the actual irreducible graph. -/
theorem primeGraph_degree_bound (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) :
    ∀ x, ((primeGraph b e D).neighborSet x).Finite ∧
      ((primeGraph b e D).neighborSet x).ncard ≤
        {z : O | ‖planarEmbedding b e z‖ ≤ D}.ncard := by
  intro x
  let δ : PrimeVertex O → O := fun y => y.val - x.val
  have hinj : Function.Injective δ := by
    intro y z hyz
    exact Subtype.ext (sub_left_injective hyz)
  have hball := planarEmbedding_finite_balls b e D
  have hmap : ∀ y ∈ (primeGraph b e D).neighborSet x,
      δ y ∈ {z : O | ‖planarEmbedding b e z‖ ≤ D} := by
    intro y hy
    change ‖planarEmbedding b e (y.val - x.val)‖ ≤ D
    simpa only [planarEmbedding_sub, norm_sub_rev] using hy.2
  exact ⟨(hball.preimage hinj.injOn).subset hmap,
    Set.ncard_le_ncard_of_injOn δ hmap hinj.injOn hball⟩

/-- Triangle inequality along actual graph walks. -/
theorem primeGraph_walk_distance (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) {x y : PrimeVertex O}
    (p : (primeGraph b e D).Walk x y) :
    ‖planarEmbedding b e x.val - planarEmbedding b e y.val‖ ≤ (p.length : ℝ) * D := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      calc
        _ ≤ ‖planarEmbedding b e x.val - planarEmbedding b e z.val‖ +
            ‖planarEmbedding b e z.val - planarEmbedding b e y.val‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ D + (p.length : ℝ) * D := add_le_add hxz.2 ih
        _ = _ := by simp [SimpleGraph.Walk.length_cons, Nat.cast_add, add_mul, add_comm]

/-- The metric exceptional graph supplies the short-walk bridge needed by
the generic restoration theorem. -/
theorem primeGraph_shortWalkBridge (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D : ℝ} (hD : 0 ≤ D)
    (E : Set (PrimeVertex O)) (B : ℕ) :
    ShortWalkBridge (primeGraph b e D) E
      ((primeGraph b e (D * (B + 1))).induce E) B := by
  intro c d hcd p hp
  refine ⟨(fun h => hcd (Subtype.ext h)), ?_⟩
  have hdist := primeGraph_walk_distance b e D p
  calc
    _ ≤ (p.length : ℝ) * D := hdist
    _ ≤ ((B + 1 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hD
    _ = D * (B + 1) := by simp [mul_comm]

/-- The selected nonunit generators determine precisely the removed
irreducibles, independently of a unique factorization assumption. -/
def selectedPrimeExceptions (generators : Finset O) : Set (PrimeVertex O) :=
  {x | x.val ∈ irreducibleExceptions (generators : Set O)}

/-- The ordinary irreducible graph injects into the actual principal avoiding
graph, so its component bound is inherited from that graph. -/
theorem ordinary_primeGraph_bound (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) (generators : Finset O) {B : ℕ}
    (hB : UniformComponentBound (latticeGraph b e D
      {x : O | ∀ a ∈ generators, ¬ a ∣ x}) B) :
    UniformComponentBound ((primeGraph b e D).induce
      (selectedPrimeExceptions generators)ᶜ) B := by
  classical
  let φ : ((primeGraph b e D).induce (selectedPrimeExceptions generators)ᶜ) →g
      latticeGraph b e D {x : O | ∀ a ∈ generators, ¬ a ∣ x} :=
    { toFun := fun x => ⟨x.val.val, by
        intro a ha hax
        exact x.property ⟨x.val.property, a, ha, hax⟩⟩
      map_rel' := by
        intro x y hxy
        refine ⟨?_, hxy.2⟩
        intro heq
        apply hxy.1
        have hval : x.val.val = y.val.val := congrArg
          (fun t : {x : O | ∀ a ∈ generators, ¬ a ∣ x} => t.val) heq
        exact Subtype.ext hval }
  apply componentBound_of_injective_hom _ _ φ _ hB
  intro x y hxy
  have hval : x.val.val = y.val.val := congrArg
    (fun t : {x : O | ∀ a ∈ generators, ¬ a ∣ x} => t.val) hxy
  exact Subtype.ext (Subtype.ext hval)

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

/-- All-order bounded-norm isolation gives the enlarged exceptional graph a
uniform component bound, including for infinite sets of unit associates. -/
theorem conductor_exception_component_bound (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (E : Set (PrimeVertex (conductorOrder K f)))
    {N R : ℝ} (hN : 0 ≤ N)
    (hE : ∀ x : E, |(Algebra.norm ℤ x.val.val : ℝ)| ≤ N) :
    ∃ M : ℕ, UniformComponentBound ((primeGraph b e R).induce E) M := by
  have hpairs := conductor_planar_finite_close_pairs K f hK hf b e (R := R) hN
  let ι : E → conductorOrder K f := fun x => x.val.val
  have hinj : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hfinit := (hpairs.image Prod.fst).preimage hinj.injOn
  have hnon : (nonisolatedVertices ((primeGraph b e R).induce E)).Finite := by
    apply hfinit.subset
    rintro x ⟨y, hxy⟩
    change x.val ≠ y.val ∧
      ‖planarEmbedding b e x.val.val - planarEmbedding b e y.val.val‖ ≤ R at hxy
    refine ⟨(x.val.val, y.val.val), ?_, rfl⟩
    refine ⟨(fun heq => hxy.1 (Subtype.ext heq)), hE x, hE y, ?_⟩
    simpa only [norm_sub_rev] using hxy.2
  exact ⟨_, uniformComponentBound_of_finite_nonisolated _ hnon⟩

/-- A finite list of nonunit principal generators bounds the actual integer
norms of all removed irreducibles. The maximum exists even for an empty list. -/
theorem selected_exception_norm_bound
    (generators : Finset (conductorOrder K f))
    (hgen : ∀ a ∈ generators, ¬ IsUnit a)
    (x : selectedPrimeExceptions generators) :
    |(Algebra.norm ℤ x.val.val : ℝ)| ≤
      ((generators.sup (fun a => (Algebra.norm ℤ a).natAbs) : ℕ) : ℝ) := by
  have hn := (exception_norm_bounds (generators : Set (conductorOrder K f))
    (generators.sup (fun a => (Algebra.norm ℤ a).natAbs)) hgen
    (fun a ha => Finset.le_sup (f := fun a => (Algebra.norm ℤ a).natAbs) ha) x.property).2
  have hcast : ((Algebra.norm ℤ x.val.val).natAbs : ℝ) ≤
      ((generators.sup (fun a => (Algebra.norm ℤ a).natAbs) : ℕ) : ℝ) := by
    exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast

/-- Complete Section 9 restoration for every actual quadratic conductor order
and every full planar embedding, conditional only on the displayed finite
principal-sieve component bound. Supplying that sieve bound remains a separate
analytic/arithmetic task; this is not a proof of `MainTarget`. -/
theorem quadraticOrder_restoration_of_principal_sieve
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D : ℝ} (hD : 0 ≤ D)
    (generators : Finset (conductorOrder K f))
    (hgen : ∀ a ∈ generators, ¬ IsUnit a) {B : ℕ}
    (hB : UniformComponentBound (latticeGraph b e D
      {x : conductorOrder K f | ∀ a ∈ generators, ¬ a ∣ x}) B) :
    ∃ Bfull : ℕ, UniformComponentBound (primeGraph b e D) Bfull := by
  let E := selectedPrimeExceptions generators
  let Δ := {z : conductorOrder K f | ‖planarEmbedding b e z‖ ≤ D}.ncard
  let H := (primeGraph b e (D * (B + 1))).induce E
  have hord := ordinary_primeGraph_bound b e D generators hB
  obtain ⟨M, hM⟩ := conductor_exception_component_bound K f hK hf b e E
    (N := ((generators.sup (fun a => (Algebra.norm ℤ a).natAbs) : ℕ) : ℝ))
    (R := D * (B + 1)) (Nat.cast_nonneg _)
    (selected_exception_norm_bound K f generators hgen)
  exact ⟨max B (M * (1 + Δ * B)), uniformComponentBound_restoration
    (primeGraph b e D) E H hord (primeGraph_degree_bound b e D) hM
    (primeGraph_shortWalkBridge b e hD E B)⟩

end Entry002
