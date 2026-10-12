import Entry002.Sieve
import Entry002.Embedding
import Mathlib.Order.KonigLemma

/-!
# Periodic components of the actual finite avoiding sieve

The last graph-theoretic step in v3 Section 2: no infinite injective walk
implies finite components, and periodicity then injects each component into
the two coefficient residues modulo the product of the selected primes.

The finite-prefix use of Kőnig's lemma follows the pinned upstream
`GaussianMoat/LatticeComponents.lean`, generalized to arbitrary integral
two-dimensional bases and full planar coordinate embeddings.
-/

namespace Entry002

open Module
open scoped BigOperators

variable {L : Type*} [AddCommGroup L]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)

/-- Every metric ball in any subset of the actual planar lattice is finite. -/
theorem latticeGraph_finite_balls (A : Set L) (root : A) (T : ℝ) :
    {x : A | ‖planarEmbedding b e x.val - planarEmbedding b e root.val‖ ≤ T}.Finite := by
  have hf := (planarEmbedding_finite_balls b e
    (T + ‖planarEmbedding b e root.val‖)).preimage
      (show Function.Injective (fun x : A => (x : L)) from Subtype.val_injective).injOn
  apply hf.subset
  intro x hx
  change ‖planarEmbedding b e x.val - planarEmbedding b e root.val‖ ≤ T at hx
  calc
    ‖planarEmbedding b e x.val‖ ≤
        ‖planarEmbedding b e x.val - planarEmbedding b e root.val‖ +
          ‖planarEmbedding b e root.val‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (planarEmbedding b e x.val - planarEmbedding b e root.val)
        (planarEmbedding b e root.val)
    _ ≤ T + ‖planarEmbedding b e root.val‖ := add_le_add hx le_rfl

/-- In particular, the actual bounded-step lattice graph is locally finite. -/
theorem latticeGraph_finite_neighbors (A : Set L) (D : ℝ) (x : A) :
    ((latticeGraph b e D A).neighborSet x).Finite := by
  apply (latticeGraph_finite_balls b e A x D).subset
  intro y hy
  change ‖planarEmbedding b e y.val - planarEmbedding b e x.val‖ ≤ D
  simpa only [norm_sub_rev] using hy.2

/-- Triangle inequality along actual lattice graph walks. -/
theorem latticeGraph_walk_distance {A : Set L} {D : ℝ} {x y : A}
    (p : (latticeGraph b e D A).Walk x y) :
    ‖planarEmbedding b e x.val - planarEmbedding b e y.val‖ ≤
      (p.length : ℝ) * max D 0 := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      calc
        _ ≤ ‖planarEmbedding b e x.val - planarEmbedding b e z.val‖ +
            ‖planarEmbedding b e z.val - planarEmbedding b e y.val‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ D + (p.length : ℝ) * max D 0 := add_le_add hxz.2 ih
        _ ≤ ((p.cons hxz).length : ℝ) * max D 0 := by
          simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
          nlinarith [le_max_left D 0]

/-- An injective path prefix, with vertices in the actual graph subtype. -/
@[ext]
structure PlanarPathPrefix (A : Set L) (D : ℝ) (root : A) (n : ℕ) where
  point : Fin (n + 1) → A
  start : point 0 = root
  injective : Function.Injective point
  step : ∀ i j, j.val = i.val + 1 → (latticeGraph b e D A).Adj (point i) (point j)

theorem PlanarPathPrefix.distance_le {A : Set L} {D : ℝ} {root : A} {n : ℕ}
    (p : PlanarPathPrefix b e A D root n) (i : Fin (n + 1)) :
    ‖planarEmbedding b e (p.point i).val - planarEmbedding b e root.val‖ ≤
      (i.val : ℝ) * max D 0 := by
  induction i using Fin.induction with
  | zero => simp [p.start]
  | succ i ih =>
      calc
        _ ≤ ‖planarEmbedding b e (p.point i.succ).val -
              planarEmbedding b e (p.point i.castSucc).val‖ +
            ‖planarEmbedding b e (p.point i.castSucc).val - planarEmbedding b e root.val‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ D + (i.val : ℝ) * max D 0 :=
          add_le_add (by simpa only [norm_sub_rev] using (p.step _ _ rfl).2) ih
        _ ≤ (i.succ.val : ℝ) * max D 0 := by
          simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
          nlinarith [le_max_left D 0]

instance PlanarPathPrefix.finite (A : Set L) (D : ℝ) (root : A) (n : ℕ) :
    Finite (PlanarPathPrefix b e A D root n) := by
  let T := (n : ℝ) * max D 0
  let S : Set (Fin (n + 1) → A) :=
    {f | ∀ i, ‖planarEmbedding b e (f i).val - planarEmbedding b e root.val‖ ≤ T}
  have hS : S.Finite := Set.Finite.pi' (fun _ => latticeGraph_finite_balls b e A root T)
  let := hS.to_subtype
  let f : PlanarPathPrefix b e A D root n → S := fun p => ⟨p.point, fun i =>
    (PlanarPathPrefix.distance_le b e p i).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt) (le_max_right D 0))⟩
  exact Finite.of_injective f (fun p q h => PlanarPathPrefix.ext (congrArg Subtype.val h))

def PlanarPathPrefix.restrict {A : Set L} {D : ℝ} {root : A} {n m : ℕ}
    (h : n ≤ m) (p : PlanarPathPrefix b e A D root m) :
    PlanarPathPrefix b e A D root n where
  point i := p.point (Fin.castLE (by omega) i)
  start := by simpa using p.start
  injective := p.injective.comp (Fin.castLE_injective (by omega))
  step i j hij := p.step _ _ hij

/-- An infinite actual lattice component gives an infinite injective edge
walk, by Kőnig's lemma for the finite sets of compatible path prefixes. -/
theorem latticeGraph_infinite_component_has_walk {A : Set L} {D : ℝ} {root : A}
    (hinfinite : (componentVertices (latticeGraph b e D A) root).Infinite) :
    ∃ w : ℕ → A, Function.Injective w ∧
      ∀ n, (latticeGraph b e D A).Adj (w n) (w (n + 1)) := by
  classical
  have hne (n : ℕ) : Nonempty (PlanarPathPrefix b e A D root n) := by
    have hnot : ¬ componentVertices (latticeGraph b e D A) root ⊆
        {y : A | ‖planarEmbedding b e y.val - planarEmbedding b e root.val‖ ≤
          (n : ℝ) * max D 0} := by
      intro h
      exact hinfinite ((latticeGraph_finite_balls b e A root
        ((n : ℝ) * max D 0)).subset h)
    obtain ⟨y, hy, hfar⟩ := Set.not_subset.mp hnot
    apply hy.elim_path
    intro path
    let p := path.val
    have hn : n ≤ p.length := by
      by_contra hn
      have hlen : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : p.length ≤ n)
      have hdist := (latticeGraph_walk_distance b e p).trans
        (mul_le_mul_of_nonneg_right hlen (le_max_right D 0))
      apply hfar
      change ‖planarEmbedding b e y.val - planarEmbedding b e root.val‖ ≤
        (n : ℝ) * max D 0
      simpa only [norm_sub_rev] using hdist
    exact ⟨{
      point := fun i => p.getVert i.val
      start := p.getVert_zero
      injective := fun i j h => Fin.ext (path.isPath.getVert_injOn
        (show i.val ≤ p.length from (Nat.le_of_lt_succ i.isLt).trans hn)
        (show j.val ≤ p.length from (Nat.le_of_lt_succ j.isLt).trans hn) h)
      step := fun i j h => by
        have hadj := p.adj_getVert_succ (i := i.val) (by omega)
        simpa only [h] using hadj
    }⟩
  let (n : ℕ) : Nonempty (PlanarPathPrefix b e A D root n) := hne n
  obtain ⟨p, hp⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => PlanarPathPrefix b e A D root n)
    (fun h => PlanarPathPrefix.restrict b e h)
    (by intro n a; apply PlanarPathPrefix.ext; funext i; rfl)
    (by intro i j k hij hjk a; apply PlanarPathPrefix.ext; funext l; rfl)
    (fun _ _ => Set.toFinite _)
  let w : ℕ → A := fun n => (p n).point (Fin.last n)
  have hagree (n k : ℕ) (hnk : n ≤ k) :
      (p k).point ⟨n, by omega⟩ = w n := by
    simpa only [PlanarPathPrefix.restrict, w, Fin.last, Fin.castLE] using
      congrArg (fun a : PlanarPathPrefix b e A D root n => a.point (Fin.last n)) (hp hnk)
  refine ⟨w, ?_, ?_⟩
  · intro n m heq
    have h := (hagree n (max n m) (le_max_left _ _)).trans
      (heq.trans (hagree m (max n m) (le_max_right _ _)).symm)
    exact congrArg Fin.val ((p (max n m)).injective h)
  · intro n
    have h := (p (n + 1)).step ⟨n, by omega⟩ (Fin.last (n + 1)) rfl
    simpa only [hagree n (n + 1) (by omega)] using h

/-- Component finiteness is derived from the no-infinite-walk conclusion. -/
theorem latticeGraph_component_finite_of_no_infinite_walk {A : Set L} {D : ℝ}
    (hno : ∀ w : ℕ → A, Function.Injective w →
      (∀ n, (latticeGraph b e D A).Adj (w n) (w (n + 1))) → False)
    (root : A) : (componentVertices (latticeGraph b e D A) root).Finite := by
  by_contra h
  obtain ⟨w, hinj, hstep⟩ := latticeGraph_infinite_component_has_walk b e h
  exact hno w hinj hstep

/-- Translation preserving the avoiding set preserves actual graph edges. -/
def latticeGraph_translation {A : Set L} {D : ℝ} (v : L)
    (hv : ∀ z ∈ A, z + v ∈ A) :
    latticeGraph b e D A →g latticeGraph b e D A where
  toFun z := ⟨z.val + v, hv z.val z.property⟩
  map_rel' := by
    intro x y hxy
    refine ⟨?_, ?_⟩
    · intro heq
      exact hxy.1 (Subtype.ext (add_right_cancel (congrArg Subtype.val heq)))
    · simpa only [planarEmbedding_add, add_sub_add_right_eq_sub] using hxy.2

/-- A finite component cannot contain distinct vertices differing by a period.
The integral basis gives the torsion-free injection of the translation orbit. -/
theorem latticeGraph_eq_of_finite_component_period {A : Set L} {D : ℝ}
    {root x y : A} {v : L}
    (hfinite : (componentVertices (latticeGraph b e D A) root).Finite)
    (hx : (latticeGraph b e D A).Reachable root x)
    (hy : (latticeGraph b e D A).Reachable root y)
    (hv : ∀ z ∈ A, z + v ∈ A) (hxy : y.val = x.val + v) : x = y := by
  classical
  by_contra hne
  have hv0 : v ≠ 0 := by
    intro h
    apply hne
    exact Subtype.ext (by simpa [h] using hxy.symm)
  have hmem (n : ℕ) : x.val + n • v ∈ A := by
    induction n with
    | zero =>
        simp only [zero_nsmul, add_zero]
        exact x.property
    | succ n ih => simpa only [succ_nsmul, add_assoc] using hv _ ih
  let f : ℕ → A := fun n => ⟨x.val + n • v, hmem n⟩
  let φ := latticeGraph_translation b e (D := D) v hv
  have hyφ : y = φ x := Subtype.ext hxy
  have hreach : (latticeGraph b e D A).Reachable x (φ x) := by
    rw [← hyφ]
    exact hx.symm.trans hy
  have hall (n : ℕ) : (latticeGraph b e D A).Reachable x (f n) := by
    induction n with
    | zero =>
        have h0 : f 0 = x := Subtype.ext (by simp [f])
        rw [h0]
    | succ n ih =>
        have heq : φ (f n) = f (n + 1) := by
          apply Subtype.ext
          change (x.val + n • v) + v = x.val + (n + 1) • v
          simp only [succ_nsmul, add_assoc]
        rw [← heq]
        exact hreach.trans (ih.map φ)
  have hvcoord : ∃ i, b.repr v i ≠ 0 := by
    by_contra h
    have hz : ∀ i, b.repr v i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    apply hv0
    apply b.ext_elem
    intro i
    simpa using hz i
  obtain ⟨i, hi⟩ := hvcoord
  have hinj : Function.Injective f := by
    intro n m h
    have hh : n • v = m • v := add_left_cancel (congrArg Subtype.val h)
    have hc := congrArg (fun z : L => b.repr z i) hh
    have hmul : (n : ℤ) * b.repr v i = (m : ℤ) * b.repr v i := by simpa using hc
    exact Nat.cast_injective (mul_right_cancel₀ hi hmul)
  apply Set.infinite_range_of_injective hinj
  exact hfinite.subset (by rintro _ ⟨n, rfl⟩; exact hx.trans (hall n))

/-- The actual two integral coefficient residues, with exactly `Q²` values. -/
def coefficientResidue (Q : ℕ) (x : L) : Fin 2 → ZMod Q := fun i => b.repr x i

/-- Equality of coefficient residues gives a translation by `Q` times a
genuine lattice vector, with no quotient-lattice premise. -/
theorem eq_add_period_of_coefficientResidue_eq {Q : ℕ} {x y : L}
    (h : coefficientResidue b Q x = coefficientResidue b Q y) :
    ∃ v : L, y = x + (Q : ℤ) • v := by
  classical
  have hdiv : ∀ i : Fin 2, (Q : ℤ) ∣ b.repr y i - b.repr x i := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ Q).mp (congrFun h i)
  choose a ha using hdiv
  let v : L := b.equivFun.symm a
  refine ⟨v, ?_⟩
  apply b.ext_elem
  intro i
  have hv : b.repr v i = a i := by
    change b.equivFun v i = a i
    exact congrFun (b.equivFun.apply_symm_apply a) i
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, hv]
  have hai := ha i
  omega

/-- Periodicity alone bounds a finite component by the actual coefficient
quotient cardinality `Q²`. -/
theorem latticeGraph_periodic_component_bound {A : Set L} {D : ℝ} {Q : ℕ}
    (hQ : Q ≠ 0) (hperiod : ∀ z ∈ A, ∀ v : L, z + (Q : ℤ) • v ∈ A)
    (root : A) (hfinite : (componentVertices (latticeGraph b e D A) root).Finite) :
    (componentVertices (latticeGraph b e D A) root).ncard ≤ Q ^ 2 := by
  classical
  let _ : NeZero Q := ⟨hQ⟩
  let C := componentVertices (latticeGraph b e D A) root
  let r : A → Fin 2 → ZMod Q := fun x => coefficientResidue b Q x.val
  have hinj : Set.InjOn r C := by
    intro x hx y hy heq
    obtain ⟨v, hv⟩ := eq_add_period_of_coefficientResidue_eq b heq
    exact latticeGraph_eq_of_finite_component_period b e hfinite hx hy
      (fun z hz => hperiod z hz v) hv
  have hcard := Set.ncard_le_card (r '' C)
  rw [Set.InjOn.ncard_image hinj, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hcard
  exact hcard

/-- Every selected residue map kills the product period, so every avoiding
class is preserved by all `Q`-lattice translations. -/
theorem avoiding_periodic (data : SignedResidueData L) (S : Finset ℕ)
    (z v : L) (hz : z ∈ avoiding data S) :
    z + ((S.prod id : ℕ) : ℤ) • v ∈ avoiding data S := by
  intro p hp
  have hcast : ((S.prod id : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem id hp)
  simpa only [map_add, map_zsmul, zsmul_eq_mul, Int.cast_natCast,
    hcast, zero_mul, add_zero] using hz p hp

/-- The complete periodic-component consequence of the analytic no-walk
conclusion for a selected genuine finite signed-prime sieve. Components are
proved finite rather than assumed finite, and their bound is the literal `Q²`.
The empty selection has `Q = 1` and is covered by the same theorem. -/
theorem avoiding_component_bound_of_no_infinite_walk
    (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (D : ℝ)
    (hno : ∀ w : ℕ → avoiding data S, Function.Injective w →
      (∀ n, (latticeGraph b e D (avoiding data S)).Adj (w n) (w (n + 1))) → False) :
    UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2) := by
  have hQ : S.prod id ≠ 0 := Nat.ne_of_gt
    (Finset.prod_pos (fun p hp => (data.prime_mem p (hS p hp)).pos))
  intro root
  have hf := latticeGraph_component_finite_of_no_infinite_walk b e hno root
  exact ⟨hf, latticeGraph_periodic_component_bound b e hQ
    (fun z hz v => avoiding_periodic data S z v hz) root hf⟩

end Entry002
