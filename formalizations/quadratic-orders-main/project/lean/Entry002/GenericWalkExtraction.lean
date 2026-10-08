import Entry002.GenericWalkGeometry

/-! Genuine subpaths of one bounded-step lattice walk, including reverse time.
This supplies the two endpoint-spanning paths used by the many-differences
argument without a covering or counting assumption. -/
set_option autoImplicit false
namespace Entry002
open Module
variable {L : Type*} [AddCommGroup L]

/-- The number of edges between two indexed walk vertices. -/
def walkSegmentLength (i j : ℕ) : ℕ := if i ≤ j then j - i else i - j

/-- Traverse the same walk from index `i` towards index `j`, in either direction. -/
def walkSegmentIndex (i j t : ℕ) : ℕ := if i ≤ j then i + t else i - t

@[simp] theorem walkSegmentIndex_zero (i j : ℕ) : walkSegmentIndex i j 0 = i := by
  simp [walkSegmentIndex]

@[simp] theorem walkSegmentIndex_endpoint (i j : ℕ) :
    walkSegmentIndex i j (walkSegmentLength i j) = j := by
  unfold walkSegmentIndex walkSegmentLength
  split <;> omega

theorem walkSegmentLength_pos {i j : ℕ} (h : i ≠ j) : 0 < walkSegmentLength i j := by
  unfold walkSegmentLength
  split <;> omega

theorem walkSegmentIndex_le {i j N t : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    (ht : t ≤ walkSegmentLength i j) : walkSegmentIndex i j t ≤ N := by
  unfold walkSegmentLength at ht
  unfold walkSegmentIndex
  split at ht <;> split <;> omega

/-- Every extracted subpath obeys the original actual-planar step bound. -/
theorem walkSegment_step (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) {N i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) {D : ℝ}
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D) :
    ∀ t < walkSegmentLength i j,
      dist (planarEmbedding b e (z (walkSegmentIndex i j t)))
        (planarEmbedding b e (z (walkSegmentIndex i j (t + 1)))) ≤ D := by
  intro t ht
  by_cases hij : i ≤ j
  · simp only [walkSegmentLength, hij, ↓reduceIte] at ht
    have hti : i + t < N := by omega
    simpa only [walkSegmentIndex, hij, ↓reduceIte, Nat.add_assoc] using hs (i + t) hti
  · simp only [walkSegmentLength, hij, ↓reduceIte] at ht
    have hti : i - (t + 1) < N := by omega
    have he : i - (t + 1) + 1 = i - t := by omega
    simpa only [walkSegmentIndex, hij, ↓reduceIte, he, dist_comm] using hs (i - (t + 1)) hti

/-- The actual vertices of an `N`-edge walk. -/
noncomputable def walkVertexSet (z : ℕ → L) (N : ℕ) : Finset L := by
  classical
  exact (Finset.range (N + 1)).image z

omit [AddCommGroup L] in
theorem walkVertex_mem (z : ℕ → L) {N t : ℕ} (ht : t ≤ N) :
    z t ∈ walkVertexSet z N := by
  classical
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩

/-- Any independent triple of vertices in one bounded-step walk forces many
actual vertex differences. The two subpaths are constructed from the walk. -/
theorem single_walk_many_differences (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) {N i j k : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D)
    (hdet : latticeDet b (z j - z i) (z k - z i) ≠ 0) :
    (latticeDet b (z j - z i) (z k - z i)).natAbs ≤
      (latticeDifferences (walkVertexSet z N)).card * (planarLatticeBall b e (4 * D)).card := by
  have hij : i ≠ j := by
    intro he
    subst j
    simp [latticeDet] at hdet
  have hik : i ≠ k := by
    intro he
    subst k
    simp [latticeDet] at hdet
  have h := lattice_walk_many_differences b e
    (fun t => z (walkSegmentIndex i j t)) (fun t => z (walkSegmentIndex i k t))
    (walkSegmentLength_pos hij) (walkSegmentLength_pos hik) (z i)
    (by simp) (by simp) (by simpa using hdet) hD
    (walkSegment_step b e z hi hj hs) (walkSegment_step b e z hi hk hs)
    (walkVertexSet z N)
    (fun t ht => walkVertex_mem z (walkSegmentIndex_le hi hj ht.le))
    (fun t ht => walkVertex_mem z (walkSegmentIndex_le hi hk ht.le))
  simpa only [walkSegmentIndex_endpoint] using h

/-- Actual Euclidean triangle area controls the number of differences of a
single bounded-step walk, with the true lattice fundamental-cell area. -/
theorem single_walk_many_differences_area (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) {N i j k : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D)
    (hdet : latticeDet b (z j - z i) (z k - z i) ≠ 0) :
    |signedPlaneDet (planarEmbedding b e (z j - z i))
      (planarEmbedding b e (z k - z i))| ≤
      ((latticeDifferences (walkVertexSet z N)).card : ℝ) *
        (planarLatticeBall b e (4 * D)).card * |planarCellDet e| := by
  have hc := single_walk_many_differences b e z hi hj hk hD hs hdet
  have hr : ((latticeDet b (z j - z i) (z k - z i)).natAbs : ℝ) ≤
      ((latticeDifferences (walkVertexSet z N)).card : ℝ) *
        (planarLatticeBall b e (4 * D)).card := by exact_mod_cast hc
  have ha : ((latticeDet b (z j - z i) (z k - z i)).natAbs : ℝ) =
      |(latticeDet b (z j - z i) (z k - z i) : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun q : ℤ => (q : ℝ))
      (Int.natCast_natAbs (latticeDet b (z j - z i) (z k - z i)))
  rw [ha] at hr
  rw [planarEmbedding_determinant, abs_mul]
  exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)


omit [AddCommGroup L] in
/-- Self-avoidance gives the actual `N+1` distinct vertices of an `N`-edge walk. -/
theorem walkVertexSet_card (z : ℕ → L) (N : ℕ)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) :
    (walkVertexSet z N).card = N + 1 := by
  classical
  unfold walkVertexSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  exact hinj i (by have hh := Finset.mem_range.mp hi; omega) j
    (by have hh := Finset.mem_range.mp hj; omega) he

/-- Every pair of vertices is at most `D*N` apart in the actual planar metric. -/
theorem bounded_walk_pair_distance (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) {N i j : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D) :
    dist (planarEmbedding b e (z i)) (planarEmbedding b e (z j)) ≤ D * N := by
  have hd := dist_le_range_sum_of_dist_le
    (f := fun t => planarEmbedding b e (z (walkSegmentIndex i j t)))
    (d := fun _ => D) (walkSegmentLength i j) (fun ht => walkSegment_step b e z hi hj hs _ ht)
  have hl : walkSegmentLength i j ≤ N := by
    unfold walkSegmentLength
    split <;> omega
  have hle : (walkSegmentLength i j : ℝ) ≤ N := by exact_mod_cast hl
  have hd' : dist (planarEmbedding b e (z i)) (planarEmbedding b e (z j)) ≤
      (walkSegmentLength i j : ℝ) * D := by
    simpa only [walkSegmentIndex_zero, walkSegmentIndex_endpoint, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] using hd
  exact hd'.trans (by nlinarith)


/-- Orthogonal changes of actual planar coordinates preserve unsigned area. -/
theorem signedPlaneDet_abs_isometry (o : Plane ≃ₗᵢ[ℝ] Plane) (x y : Plane) :
    |signedPlaneDet (o x) (o y)| = |signedPlaneDet x y| := by
  have hid (u v : Plane) : (signedPlaneDet u v)^2 =
      ‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2 := by
    simp only [signedPlaneDet, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      star_trivial]
    ring
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
  rw [hid, hid, o.norm_map, o.norm_map, o.inner_map_map]

@[simp] theorem planarCellDet_abs_isometry (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (o : Plane ≃ₗᵢ[ℝ] Plane) : |planarCellDet (e.trans o.toLinearEquiv)| = |planarCellDet e| :=
  signedPlaneDet_abs_isometry o _ _

@[simp] theorem planarEmbedding_isometry (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (x : L) :
    planarEmbedding b (e.trans o.toLinearEquiv) x = o (planarEmbedding b e x) := rfl

@[simp] theorem planarLatticeBall_isometry (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (D : ℝ) :
    planarLatticeBall b (e.trans o.toLinearEquiv) D = planarLatticeBall b e D := by
  classical
  ext x
  simp only [mem_planarLatticeBall, planarEmbedding_isometry, o.norm_map]

/-- Direct manuscript application: an oriented diameter endpoint at `(R,0)`
and a walk vertex at transverse distance `W` give the actual `R*W` difference
bound. The paths are extracted from this single walk in either time direction. -/
theorem single_walk_diameter_transverse_many_differences (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (z : ℕ → L)
    {N i j k : ℕ} (hi : i ≤ N) (hj : j ≤ N) (hk : k ≤ N)
    {D R W : ℝ} (hD : 0 ≤ D) (hR : 0 < R) (hW : 0 < W)
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D)
    (hjr : (o (planarEmbedding b e (z j - z i))) 0 = R)
    (hji : (o (planarEmbedding b e (z j - z i))) 1 = 0)
    (hki : |(o (planarEmbedding b e (z k - z i))) 1| = W) :
    R * W ≤ ((latticeDifferences (walkVertexSet z N)).card : ℝ) *
      (planarLatticeBall b e (4 * D)).card * |planarCellDet e| := by
  have harea : |signedPlaneDet
      (planarEmbedding b (e.trans o.toLinearEquiv) (z j - z i))
      (planarEmbedding b (e.trans o.toLinearEquiv) (z k - z i))| = R * W := by
    simp only [planarEmbedding_isometry, signedPlaneDet, hjr, hji, zero_mul, sub_zero,
      abs_mul, abs_of_pos hR, hki]
  have hd : latticeDet b (z j - z i) (z k - z i) ≠ 0 := by
    intro he
    rw [planarEmbedding_determinant, he, Int.cast_zero, zero_mul, abs_zero] at harea
    exact (mul_pos hR hW).ne' harea.symm
  have hs' : ∀ t < N, dist (planarEmbedding b (e.trans o.toLinearEquiv) (z t))
      (planarEmbedding b (e.trans o.toLinearEquiv) (z (t + 1))) ≤ D := by
    simpa only [planarEmbedding_isometry, o.dist_map] using hs
  have h := single_walk_many_differences_area b (e.trans o.toLinearEquiv) z hi hj hk hD hs' hd
  simpa only [harea, planarLatticeBall_isometry, planarCellDet_abs_isometry] using h


/-- Exact greatest actual transverse distance among the finite walk vertices. -/
noncomputable def walkTransverseMax (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane)
    (z : ℕ → L) (N i : ℕ) : ℝ :=
  (Finset.range (N + 1)).sup' (Finset.nonempty_range_iff.mpr (by omega))
    (fun t => |(o (planarEmbedding b e (z t - z i))) 1|)

noncomputable def walkTransverseWidth (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane)
    (z : ℕ → L) (N i : ℕ) : ℝ := max 1 (walkTransverseMax b e o z N i)

theorem walkTransverseMax_attained (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (z : ℕ → L) (N i : ℕ) :
    ∃ k ≤ N, walkTransverseMax b e o z N i = |(o (planarEmbedding b e (z k - z i))) 1| := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (show N + 1 ≠ 0 by omega))
    (fun t => |(o (planarEmbedding b e (z t - z i))) 1|)
  exact ⟨k, by have hh := Finset.mem_range.mp hk; omega, he⟩

theorem walkTransverse_le_width (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (z : ℕ → L)
    {N i t : ℕ} (ht : t ≤ N) :
    |(o (planarEmbedding b e (z t - z i))) 1| ≤ walkTransverseWidth b e o z N i := by
  have hh : |(o (planarEmbedding b e (z t - z i))) 1| ≤ walkTransverseMax b e o z N i :=
    Finset.le_sup' (fun q => |(o (planarEmbedding b e (z q - z i))) 1|)
      (Finset.mem_range.mpr (by omega))
  exact hh.trans (le_max_right _ _)

/-- A translate of a nonempty finite set injects into its actual difference set. -/
theorem latticeDifferences_card_ge (V : Finset L) {p : L} (hp : p ∈ V) :
    V.card ≤ (latticeDifferences V).card := by
  classical
  have hi : Function.Injective (fun x : L => x - p) := by
    intro x y h
    simpa only [sub_add_cancel] using congrArg (fun q : L => q + p) h
  rw [← Finset.card_image_of_injective V hi]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact sub_mem_latticeDifferences V hy hp

/-- The complete many-differences lower bound with the actual maximum
transverse width, including the narrow-width case `W=1`. -/
theorem single_walk_many_differences_width (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (z : ℕ → L)
    {N i j : ℕ} (hi : i ≤ N) (hj : j ≤ N)
    {D R : ℝ} (hD : 0 ≤ D) (hR : 0 < R)
    (hs : ∀ t < N, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t + 1))) ≤ D)
    (hinj : ∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j)
    (hjr : (o (planarEmbedding b e (z j - z i))) 0 = R)
    (hji : (o (planarEmbedding b e (z j - z i))) 1 = 0) :
    R * walkTransverseWidth b e o z N i ≤
      max 1 (max D ((planarLatticeBall b e (4 * D)).card * |planarCellDet e|)) *
        (latticeDifferences (walkVertexSet z N)).card := by
  let K : ℝ := max 1 (max D ((planarLatticeBall b e (4 * D)).card * |planarCellDet e|))
  have hKD : D ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : (planarLatticeBall b e (4 * D)).card * |planarCellDet e| ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases hwidth : walkTransverseMax b e o z N i ≤ 1
  · have hW : walkTransverseWidth b e o z N i = 1 := max_eq_left hwidth
    rw [hW, mul_one]
    have hpair := bounded_walk_pair_distance b e z hi hj hD hs
    have hn : ‖o (planarEmbedding b e (z j - z i))‖ = R := by
      have hh := EuclideanSpace.real_norm_sq_eq (o (planarEmbedding b e (z j - z i)))
      simp only [Fin.sum_univ_two, hjr, hji] at hh
      nlinarith [norm_nonneg (o (planarEmbedding b e (z j - z i)))]
    have hRN : R ≤ D * N := by
      rw [o.norm_map, planarEmbedding_sub_signed, ← dist_eq_norm, dist_comm] at hn
      simpa only [hn] using hpair
    have hc := latticeDifferences_card_ge (walkVertexSet z N) (walkVertex_mem z (show 0 ≤ N by omega))
    rw [walkVertexSet_card z N hinj] at hc
    have hNc : (N : ℝ) ≤ (latticeDifferences (walkVertexSet z N)).card := by
      exact_mod_cast (show N ≤ (latticeDifferences (walkVertexSet z N)).card by omega)
    exact hRN.trans ((mul_le_mul_of_nonneg_left hNc hD).trans
      (mul_le_mul_of_nonneg_right hKD (Nat.cast_nonneg _)))
  · have hW : walkTransverseWidth b e o z N i = walkTransverseMax b e o z N i :=
      max_eq_right (le_of_lt (lt_of_not_ge hwidth))
    obtain ⟨k, hk, he⟩ := walkTransverseMax_attained b e o z N i
    have hp : 0 < walkTransverseWidth b e o z N i := by
      dsimp [walkTransverseWidth]
      exact zero_lt_one.trans_le (le_max_left _ _)
    have h := single_walk_diameter_transverse_many_differences b e o z hi hj hk hD hR hp
      hs hjr hji (hW.trans he).symm
    have hle := mul_le_mul_of_nonneg_left hKB
      (show 0 ≤ ((latticeDifferences (walkVertexSet z N)).card : ℝ) from Nat.cast_nonneg _)
    exact h.trans (by simpa only [K, mul_assoc, mul_comm, mul_left_comm] using hle)

end Entry002
