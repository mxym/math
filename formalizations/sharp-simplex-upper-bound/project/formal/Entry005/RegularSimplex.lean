import Entry005.AffineNormalization

noncomputable section
open Metric
open scoped BigOperators
namespace Entry005

private def ones (d : ℕ) : Space (d + 1) := WithLp.toLp 2 (fun _ => 1)
private def radiusScale (d : ℕ) : ℝ := Real.sqrt ((d : ℝ) * (d + 1))
private def rawVertex (d : ℕ) (i : Fin (d + 1)) : Space (d + 1) :=
  radiusScale d • (EuclideanSpace.single i 1 - (d + 1 : ℝ)⁻¹ • ones d)
private abbrev Model (d : ℕ) := (ℝ ∙ ones d)ᗮ

private theorem ones_ne_zero (d : ℕ) : ones d ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space (d + 1) => x 0) h
  simp [ones] at he

private def modelIso (d : ℕ) : Model d ≃ₗᵢ[ℝ] Space d := by
  letI : Fact (Module.finrank ℝ (Space (d + 1)) = d + 1) := ⟨by simp [Space]⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton d (ones_ne_zero d)).repr

private theorem scale_pos {d : ℕ} (hd : 1 ≤ d) : 0 < radiusScale d := by
  unfold radiusScale
  apply Real.sqrt_pos.mpr
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

private theorem scale_sq (d : ℕ) : radiusScale d ^ 2 = (d : ℝ) * (d + 1) := by
  apply Real.sq_sqrt
  positivity

private theorem inner_ones (d : ℕ) (x : Space (d + 1)) :
    inner ℝ (ones d) x = ∑ j, x j := by
  simp [ones, PiLp.inner_apply, RCLike.inner_apply]

private theorem raw_mem (d : ℕ) (i : Fin (d + 1)) : rawVertex d i ∈ Model d := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [rawVertex, inner_smul_right, inner_sub_right, inner_smul_right, inner_ones,
    inner_ones]
  have hn : (d + 1 : ℝ) ≠ 0 := by positivity
  simp [ones, PiLp.single_apply, Finset.sum_ite_eq', hn]

private def modelVertex (d : ℕ) (i : Fin (d + 1)) : Model d := ⟨rawVertex d i, raw_mem d i⟩

private theorem raw_independent {d : ℕ} (hd : 1 ≤ d) : AffineIndependent ℝ (rawVertex d) := by
  let f : Space (d + 1) ≃ᵃ[ℝ] Space (d + 1) := AffineEquiv.ofLinearEquiv
    (LinearEquiv.smulOfNeZero ℝ _ (radiusScale d) (scale_pos hd).ne')
    ((d + 1 : ℝ)⁻¹ • ones d) 0
  have hbase := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis.linearIndependent.affineIndependent
  have hmap := hbase.map' f.toAffineMap f.injective
  change AffineIndependent ℝ (fun i => radiusScale d •
    (EuclideanSpace.single i 1 - (d + 1 : ℝ)⁻¹ • ones d))
  simpa [Function.comp_def, f, EuclideanSpace.basisFun_apply, rawVertex,
    vsub_eq_sub, vadd_eq_add] using hmap

private def modelSimplex (d : ℕ) (hd : 1 ≤ d) : Affine.Simplex ℝ (Model d) d where
  points := modelVertex d
  independent := by
    apply AffineIndependent.of_comp (Model d).subtype.toAffineMap
    exact raw_independent hd

private def modelMap (d : ℕ) : Model d →ᵃ[ℝ] Space d :=
  (modelIso d).toLinearEquiv.toAffineEquiv.toAffineMap

/-- A concrete regular simplex with unit inradius, transported by an actual linear isometry. -/
def regularSimplex (d : ℕ) (hd : 1 ≤ d) : Affine.Simplex ℝ (Space d) d :=
  (modelSimplex d hd).map (modelMap d)
    (fun _ _ h => (modelIso d).injective h)

private theorem raw_norm {d : ℕ} (hd : 1 ≤ d) (i : Fin (d + 1)) :
    ‖rawVertex d i‖ = d := by
  have hinner : inner ℝ (rawVertex d i) (rawVertex d i) = (d : ℝ)^2 := by
    have hc : (d + 1 : ℝ) ≠ 0 := by positivity
    have hoo : inner ℝ (ones d) (ones d) = (d + 1 : ℝ) := by
      rw [inner_ones]
      simp [ones]
    have hso : inner ℝ (EuclideanSpace.single i 1) (ones d) = 1 := by
      simp [EuclideanSpace.inner_single_left, ones]
    have hos : inner ℝ (ones d) (EuclideanSpace.single i 1) = 1 := by
      simp [inner_ones, PiLp.single_apply, Finset.sum_ite_eq']
    have hss : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i 1) = 1 := by
      simp
    simp only [rawVertex, real_inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, hss, hso, hos, hoo]
    rw [inv_mul_cancel₀ hc]
    simp only [sub_self, mul_zero, sub_zero, mul_one]
    calc
      radiusScale d * (radiusScale d * (1 - (d + 1 : ℝ)⁻¹)) =
          radiusScale d ^ 2 * (1 - (d + 1 : ℝ)⁻¹) := by ring
      _ = (d : ℝ)^2 := by rw [scale_sq]; field_simp; ring
  rw [real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (rawVertex d i), (show (0 : ℝ) ≤ d by positivity)]

/-- Every actual vertex has norm exactly the dimension. -/
theorem regularSimplex_vertex_norm (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    ‖(regularSimplex d hd).points i‖ = d := by
  change ‖modelIso d (modelVertex d i)‖ = d
  rw [(modelIso d).norm_map]
  exact raw_norm hd i

private theorem raw_sum (d : ℕ) : ∑ i, rawVertex d i = 0 := by
  ext j
  have hn : (d + 1 : ℝ) ≠ 0 := by positivity
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawVertex, PiLp.smul_apply,
    PiLp.sub_apply, ones, PiLp.single_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq, hn]

private theorem model_sum (d : ℕ) : ∑ i, modelVertex d i = 0 := by
  apply Subtype.ext
  change (↑(∑ i, modelVertex d i) : Space (d + 1)) = 0
  rw [Submodule.coe_sum]
  exact raw_sum d

/-- The actual simplex centroid is the origin. -/
theorem regularSimplex_centroid (d : ℕ) (hd : 1 ≤ d) :
    (regularSimplex d hd).centroid = 0 := by
  have hc : (modelSimplex d hd).centroid = 0 := by
    have h := (modelSimplex d hd).centroid_vsub_eq (0 : Model d)
    simpa only [vsub_eq_sub, sub_zero, modelSimplex, model_sum, smul_zero] using h
  have hm := (modelSimplex d hd).centroid_map (modelMap d)
    (fun _ _ h => (modelIso d).injective h)
  change (regularSimplex d hd).centroid = modelMap d (modelSimplex d hd).centroid at hm
  rw [hm, hc]
  exact (modelIso d).map_zero

private theorem raw_inner_model (d : ℕ) (i : Fin (d + 1)) (x : Model d) :
    inner ℝ (rawVertex d i) (x : Space (d + 1)) = radiusScale d * (x : Space (d + 1)) i := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  rw [rawVertex, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hx]
  simp [EuclideanSpace.inner_single_left]

private theorem model_ball {d : ℕ} (hd : 1 ≤ d) (x : Model d) (hx : ‖x‖ ≤ 1) :
    x ∈ convexHull ℝ (Set.range (modelVertex d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < d + 1 := by positivity
  have hdenpos : 0 < (d : ℝ) * (d + 1) := mul_pos hdpos hnpos
  have hsumx : ∑ j, (x : Space (d + 1)) j = 0 := by
    rw [← inner_ones]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  let w : Fin (d + 1) → ℝ := fun i =>
    (radiusScale d * (x : Space (d + 1)) i + d) / ((d : ℝ) * (d + 1))
  have hw0 (i : Fin (d + 1)) : 0 ≤ w i := by
    have hnorm : ‖modelVertex d i‖ = d := raw_norm hd i
    have hCS := abs_real_inner_le_norm (modelVertex d i) x
    rw [hnorm, Submodule.coe_inner] at hCS
    change |inner ℝ (rawVertex d i) (x : Space (d + 1))| ≤ (d : ℝ) * ‖x‖ at hCS
    rw [raw_inner_model] at hCS
    have hb := neg_abs_le (radiusScale d * (x : Space (d + 1)) i)
    have hm : (d : ℝ) * ‖x‖ ≤ d := by simpa using mul_le_mul_of_nonneg_left hx hdpos.le
    apply div_nonneg _ hdenpos.le
    dsimp [w]
    linarith
  have hw1 : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hsumx]
    simp only [mul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, zero_add]
    field_simp
  apply mem_convexHull_of_exists_fintype (s := Set.range (modelVertex d)) w (modelVertex d)
    hw0 hw1 (fun i => ⟨i, rfl⟩)
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ∑ i, w i • rawVertex d i = (x : Space (d + 1))
  ext j
  simp only [WithLp.ofLp_sum, Finset.sum_apply, rawVertex, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.single_apply, ones, smul_eq_mul]
  simp_rw [mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib]
  have hf : (∑ i, w i * radiusScale d * (if j = i then (1 : ℝ) else 0)) =
      w j * radiusScale d := by simp [mul_ite, Finset.sum_ite_eq]
  have hg : (∑ i, w i * radiusScale d * (d + 1 : ℝ)⁻¹ * 1) =
      (∑ i, w i) * radiusScale d * (d + 1 : ℝ)⁻¹ := by
    simp only [mul_one, Finset.sum_mul]
  rw [hf, hg, hw1]
  dsimp [w]
  field_simp [hdpos.ne', hnpos.ne']
  linear_combination (x : Space (d + 1)) j * scale_sq d

/-- The actual unit closed ball is contained in the actual simplex hull. -/
theorem regularSimplex_unit_ball (d : ℕ) (hd : 1 ≤ d) :
    closedBall (0 : Space d) 1 ⊆ simplexSet (regularSimplex d hd) := by
  intro x hx
  let y : Model d := (modelIso d).symm x
  have hy : ‖y‖ ≤ 1 := by
    simpa only [y, (modelIso d).symm.norm_map, mem_closedBall, dist_zero_right] using hx
  have hmem := model_ball hd y hy
  have him : modelMap d y = x := (modelIso d).apply_symm_apply x
  rw [← him]
  change modelMap d y ∈ convexHull ℝ (Set.range (modelMap d ∘ (modelSimplex d hd).points))
  rw [Set.range_comp, ← (modelMap d).image_convexHull]
  exact ⟨y, hmem, rfl⟩

private theorem raw_dist_sq (d : ℕ) (i j : Fin (d + 1)) (hij : i ≠ j) :
    dist (rawVertex d i) (rawVertex d j) ^ 2 = 2 * (d : ℝ) * (d + 1) := by
  have hdif : rawVertex d i - rawVertex d j =
      radiusScale d • (EuclideanSpace.single i 1 - EuclideanSpace.single j 1) := by
    simp only [rawVertex, smul_sub]
    abel
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, hdif]
  simp only [real_inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  have hcross : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) = 0 := by
    simp [EuclideanSpace.inner_single_left, hij]
  have hcross' : inner ℝ (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i 1) = 0 := by
    simp [EuclideanSpace.inner_single_left, hij.symm]
  have hss (k : Fin (d + 1)) :
      inner ℝ (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single k 1) = 1 := by simp
  simp only [hcross, hcross', hss, sub_zero, zero_sub]
  calc
    radiusScale d * (radiusScale d * 1 - radiusScale d * -1) = 2 * radiusScale d ^ 2 := by ring
    _ = 2 * (d : ℝ) * (d + 1) := by rw [scale_sq]; ring

/-- Every distinct pair of actual vertices has the same explicit positive edge length. -/
theorem regularSimplex_edge_length (d : ℕ) (hd : 1 ≤ d) (i j : Fin (d + 1))
    (hij : i ≠ j) :
    dist ((regularSimplex d hd).points i) ((regularSimplex d hd).points j) =
      Real.sqrt (2 * (d : ℝ) * (d + 1)) := by
  have he : dist ((regularSimplex d hd).points i) ((regularSimplex d hd).points j) =
      dist (rawVertex d i) (rawVertex d j) := by
    change dist (modelIso d (modelVertex d i)) (modelIso d (modelVertex d j)) = _
    rw [(modelIso d).dist_map]
    rfl
  rw [he]
  have hs := raw_dist_sq d i j hij
  have hp : 0 ≤ 2 * (d : ℝ) * (d + 1) := by positivity
  have hr := Real.sq_sqrt hp
  nlinarith [dist_nonneg (x := rawVertex d i) (y := rawVertex d j),
    Real.sqrt_nonneg (2 * (d : ℝ) * (d + 1))]

/-- The exact off-diagonal Gram identity supplies the actual facet inequalities. -/
theorem regularSimplex_vertex_inner (d : ℕ) (hd : 1 ≤ d) (i j : Fin (d + 1))
    (hij : i ≠ j) :
    inner ℝ ((regularSimplex d hd).points i) ((regularSimplex d hd).points j) = -(d : ℝ) := by
  change inner ℝ (modelIso d (modelVertex d i)) (modelIso d (modelVertex d j)) = _
  rw [(modelIso d).inner_map_map, Submodule.coe_inner]
  change inner ℝ (rawVertex d i) (modelVertex d j : Space (d + 1)) = _
  rw [raw_inner_model]
  have hn : (d + 1 : ℝ) ≠ 0 := by positivity
  simp only [modelVertex, rawVertex, PiLp.smul_apply, PiLp.sub_apply, PiLp.single_apply,
    ones, smul_eq_mul]
  simp only [ite_eq_right hij, zero_sub, mul_neg]
  field_simp
  linear_combination -(scale_sq d)

/-- Every point of the actual hull satisfies each exact regular-simplex facet inequality. -/
theorem regularSimplex_facet_bound (d : ℕ) (hd : 1 ≤ d) (i : Fin (d + 1))
    {x : Space d} (hx : x ∈ simplexSet (regularSimplex d hd)) :
    -(d : ℝ) ≤ inner ℝ ((regularSimplex d hd).points i) x := by
  let C : Set (Space d) := {x | -(d : ℝ) ≤ inner ℝ ((regularSimplex d hd).points i) x}
  have hc : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    change -(d : ℝ) ≤ inner ℝ ((regularSimplex d hd).points i) (a • x + b • y)
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  have hv : Set.range (regularSimplex d hd).points ⊆ C := by
    rintro x ⟨j, rfl⟩
    by_cases hij : i = j
    · subst j
      change -(d : ℝ) ≤ inner ℝ ((regularSimplex d hd).points i) ((regularSimplex d hd).points i)
      rw [real_inner_self_eq_norm_sq, regularSimplex_vertex_norm]
      nlinarith [show (0 : ℝ) ≤ d by positivity]
    · change -(d : ℝ) ≤ inner ℝ ((regularSimplex d hd).points i) ((regularSimplex d hd).points j)
      rw [regularSimplex_vertex_inner d hd i j hij]
  exact convexHull_min hv hc hx

/-- Unit inradius is exact: no larger closed ball with center zero lies in this hull. -/
theorem regularSimplex_centered_ball_iff (d : ℕ) (hd : 1 ≤ d) (r : ℝ) :
    closedBall (0 : Space d) r ⊆ simplexSet (regularSimplex d hd) ↔ r ≤ 1 := by
  constructor
  · intro hball
    by_cases hr : r ≤ 0
    · linarith
    have hrpos : 0 < r := lt_of_not_ge hr
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    let x : Space d := (-(r / d)) • (regularSimplex d hd).points 0
    have hnorm : ‖x‖ = r := by
      dsimp [x]
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hrpos hdpos),
        regularSimplex_vertex_norm, div_mul_cancel₀ r hdpos.ne']
    have hx : x ∈ simplexSet (regularSimplex d hd) := hball (by
      simpa only [mem_closedBall, dist_zero_right, hnorm] using le_refl r)
    have hf := regularSimplex_facet_bound d hd 0 hx
    dsimp [x] at hf
    rw [inner_smul_right, real_inner_self_eq_norm_sq, regularSimplex_vertex_norm] at hf
    have he : -(r / (d : ℝ)) * (d : ℝ)^2 = -r * d := by field_simp
    rw [he] at hf
    nlinarith
  · intro hr
    exact (closedBall_subset_closedBall hr).trans (regularSimplex_unit_ball d hd)

/-- Every full-dimensional simplex is genuinely affinely equivalent to the constructed model. -/
theorem exists_regular_unit_normalization {d : ℕ} (hd : 1 ≤ d)
    (S : Affine.Simplex ℝ (Space d) d) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      affineSimplex f S = regularSimplex d hd ∧
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      (∀ i, ‖(affineSimplex f S).points i‖ = d) ∧
      (∀ i j, i ≠ j → dist ((affineSimplex f S).points i) ((affineSimplex f S).points j) =
        Real.sqrt (2 * (d : ℝ) * (d + 1))) := by
  let f := simplexAffineEquiv S (regularSimplex d hd)
  have hf : affineSimplex f S = regularSimplex d hd := by
    apply Affine.Simplex.ext
    intro i
    exact simplexAffineEquiv_points S (regularSimplex d hd) i
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact regularSimplex_centroid d hd
  · rw [hf]
    exact regularSimplex_unit_ball d hd
  · rw [hf]
    exact regularSimplex_vertex_norm d hd
  · rw [hf]
    exact regularSimplex_edge_length d hd

/-- A prescribed genuine maximum simplex admits the exact regular normalization, and its
original-centroid excess is preserved by the same actual affine equivalence. -/
theorem maximum_simplex_regular_normalization {d : ℕ} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (S : Affine.Simplex ℝ (Space d) d)
    (hmax : maximumInscribed K S) :
    ∃ f : Space d ≃ᵃ[ℝ] Space d,
      affineSimplex f S = regularSimplex d hd ∧
      (affineSimplex f S).centroid = 0 ∧
      closedBall (0 : Space d) 1 ⊆ simplexSet (affineSimplex f S) ∧
      (∀ i, ‖(affineSimplex f S).points i‖ = d) ∧
      maximumInscribed (affineBody f K) (affineSimplex f S) ∧
      excess (affineBody f K : Set (Space d)) (affineSimplex f S) =
        excess (K : Set (Space d)) S := by
  obtain ⟨f, he, hc, hb, hn, _⟩ := exists_regular_unit_normalization hd S
  exact ⟨f, he, hc, hb, hn, (maximumInscribed_affine_iff f K S).mpr hmax,
    excess_affine_image S f (K : Set (Space d))⟩

end Entry005
