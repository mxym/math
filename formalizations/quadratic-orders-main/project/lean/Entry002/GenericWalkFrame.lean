import Entry002.GenericWalkPacking
import Mathlib.Analysis.Complex.Isometry

/-! Actual finite-walk diameter frames, with all metric constants retained.
The complex diameter rotation is adapted from the pinned upstream-028
GaussianMoat/DifferenceSampling.lean, lines 97--108. -/
set_option autoImplicit false
namespace Entry002
open Module
variable {L : Type*} [AddCommGroup L]

/-- An actual finite set of walk vertices has an attained diameter pair. -/
theorem walk_diameter_pair (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) (N : ℕ) :
    ∃ i ≤ N, ∃ j ≤ N, ∀ k ≤ N, ∀ l ≤ N,
      dist (planarEmbedding b e (z k)) (planarEmbedding b e (z l)) ≤
        dist (planarEmbedding b e (z i)) (planarEmbedding b e (z j)) := by
  classical
  let I := Finset.range (N + 1)
  have hI : I.Nonempty := ⟨0, by simp [I]⟩
  obtain ⟨⟨i,j⟩, hij, hmax⟩ := Finset.exists_max_image (I ×ˢ I)
    (fun q => dist (planarEmbedding b e (z q.1)) (planarEmbedding b e (z q.2)))
    (hI.product hI)
  have hi : i ≤ N := by have h := (Finset.mem_product.mp hij).1; simp [I] at h; omega
  have hj : j ≤ N := by have h := (Finset.mem_product.mp hij).2; simp [I] at h; omega
  refine ⟨i, hi, j, hj, ?_⟩
  intro k hk l hl
  exact hmax (k,l) (by simp [I, hk, hl])

noncomputable def actualDiameterRotation (a : ℂ) : ℂ := star a / (‖a‖ : ℂ)

theorem actualDiameterRotation_norm {a : ℂ} (ha : a ≠ 0) :
    ‖actualDiameterRotation a‖ = 1 := by
  simp [actualDiameterRotation, Complex.norm_real, norm_ne_zero_iff.mpr ha]

theorem actualDiameterRotation_mul (a : ℂ) : actualDiameterRotation a * a = (‖a‖ : ℂ) := by
  by_cases ha : a = 0
  · simp [ha, actualDiameterRotation]
  have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hm : star a * a = (‖a‖ : ℂ)^2 := Complex.conj_mul' a
  rw [actualDiameterRotation, div_mul_eq_mul_div, hm]
  field_simp

/-- Every nonzero actual planar vector can be made horizontal by a genuine
real linear isometry of the plane. Its actual length is preserved. -/
theorem exists_diameter_orientation (x : Plane) (hx : x ≠ 0) :
    ∃ o : Plane ≃ₗᵢ[ℝ] Plane, (o x) 0 = ‖x‖ ∧ (o x) 1 = 0 := by
  let a : ℂ := planeComplex x
  have ha : a ≠ 0 := by
    intro h
    apply hx
    apply planeComplex.injective
    simpa [a] using h
  let u : Circle := ⟨actualDiameterRotation a, by
    exact mem_sphere_zero_iff_norm.mpr (actualDiameterRotation_norm ha)⟩
  let o : Plane ≃ₗᵢ[ℝ] Plane := planeComplex.trans ((rotation u).trans planeComplex.symm)
  have ho : planeComplex (o x) = (‖a‖ : ℂ) := by
    calc
      planeComplex (o x) = (rotation u) (planeComplex x) := by
        simp only [o, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
      _ = actualDiameterRotation a * a := rfl
      _ = (‖a‖ : ℂ) := actualDiameterRotation_mul a
  refine ⟨o, ?_, ?_⟩
  · have h := congrArg Complex.re ho
    simpa only [planeComplex_re, Complex.ofReal_re, a, planeComplex.norm_map] using h
  · have h := congrArg Complex.im ho
    simpa only [planeComplex_im, Complex.ofReal_im] using h

/-- The diameter inequalities force all projections to lie between the
endpoints, and all actual transverse distances to be at most the diameter. -/
theorem oriented_diameter_rectangle (o : Plane ≃ₗᵢ[ℝ] Plane) {a v : Plane} {r : ℝ}
    (har : (o a) 0 = r) (_hai : (o a) 1 = 0)
    (hv : ‖v‖ ≤ r) (hva : ‖v - a‖ ≤ r) :
    0 ≤ (o v) 0 ∧ (o v) 0 ≤ r ∧ |(o v) 1| ≤ r := by
  have hn : ‖o v‖ ≤ r := by simpa only [o.norm_map] using hv
  have hna : ‖o v - o a‖ ≤ r := by simpa only [← map_sub, o.norm_map] using hva
  have hr := Complex.abs_re_le_norm (planeComplex (o v))
  have hi := Complex.abs_im_le_norm (planeComplex (o v))
  have hra := Complex.abs_re_le_norm (planeComplex (o v - o a))
  simp only [planeComplex_re, planeComplex_im, planeComplex.norm_map, PiLp.sub_apply, har] at hr hi hra
  have hl := (abs_le.mp (hra.trans hna)).1
  exact ⟨by linarith, (le_abs_self _).trans (hr.trans hn), hi.trans hn⟩


/-- Subtracting two vertices in an actual diameter rectangle gives an
origin-centered actual difference rectangle with half-width `2W`. -/
theorem lattice_differences_rectangle (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane)
    (V : Finset L) {R W : ℝ}
    (hV : ∀ x ∈ V, 0 ≤ (o (planarEmbedding b e x - c)) 0 ∧
      (o (planarEmbedding b e x - c)) 0 ≤ R ∧ |(o (planarEmbedding b e x - c)) 1| ≤ W) :
    ∀ x ∈ latticeDifferences V, x ∈ latticeRectangle b e o R (2 * W) := by
  classical
  intro w hw
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  obtain ⟨hx0,hxR,hxW⟩ := hV x hx
  obtain ⟨hy0,hyR,hyW⟩ := hV y hy
  have he : o (planarEmbedding b e (x - y)) =
      o (planarEmbedding b e x - c) - o (planarEmbedding b e y - c) := by
    rw [planarEmbedding_sub_signed, ← map_sub]
    congr 1
    abel
  change |o (planarEmbedding b e (x-y)) 0| ≤ R ∧ |o (planarEmbedding b e (x-y)) 1| ≤ 2 * W
  rw [he]
  simp only [PiLp.sub_apply]
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact (abs_sub _ _).trans (by linarith)

/-- All geometric conclusions for one actual self-avoiding bounded-step walk.
The constants `C` and `H` are fixed by the supplied full lattice before any
walk, step bound, or starting point is chosen. -/
structure ActualWalkFrame (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (N : ℕ) (D C H : ℝ) where
  orientation : Plane ≃ₗᵢ[ℝ] Plane
  originIndex : ℕ
  endpointIndex : ℕ
  originIndex_le : originIndex ≤ N
  endpointIndex_le : endpointIndex ≤ N
  center : Plane
  center_eq : center = planarEmbedding b e (z originIndex)
  diameter : ℝ
  diameter_eq : diameter = dist (planarEmbedding b e (z originIndex))
    (planarEmbedding b e (z endpointIndex))
  diameter_pos : 0 < diameter
  diameter_maximal : ∀ i ≤ N, ∀ j ≤ N,
    dist (planarEmbedding b e (z i)) (planarEmbedding b e (z j)) ≤ diameter
  length : ℝ
  length_eq : length = max 1 diameter
  width : ℝ
  width_eq : width = walkTransverseWidth b e orientation z N originIndex
  endpoint_horizontal : orientation (planarEmbedding b e (z endpointIndex - z originIndex)) 0 = diameter
  endpoint_transverse_zero : orientation (planarEmbedding b e (z endpointIndex - z originIndex)) 1 = 0
  one_le_width : 1 ≤ width
  width_le_length : width ≤ length
  rectangle : ∀ x ∈ walkVertexSet z N,
    0 ≤ (orientation (planarEmbedding b e x - center)) 0 ∧
      (orientation (planarEmbedding b e x - center)) 0 ≤ length ∧
      |(orientation (planarEmbedding b e x - center)) 1| ≤ width
  difference_rectangle : ∀ x ∈ latticeDifferences (walkVertexSet z N),
    x ∈ latticeRectangle b e orientation length (2 * width)
  packing : (N + 1 : ℝ) ≤ C * length * width
  diameter_step : diameter ≤ D * N
  length_step_max : length ≤ max 1 (D * N)
  length_step : length ≤ H * D * N
  area_upper : length * width ≤ H^2 * D^2 * (N : ℝ)^2
  area_differences : length * width ≤
    H * max 1 (max D ((planarLatticeBall b e (4 * D)).card * |planarCellDet e|)) *
      (latticeDifferences (walkVertexSet z N)).card

/-- Every positive-length actual self-avoiding walk admits a diameter frame
and all manuscript packing/many-differences bounds, with fixed lattice factors.
`length=max 1 diameter` handles lattices with shortest vector below one. -/
theorem actual_walk_frame_package (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C H : ℝ, 0 < C ∧ 1 ≤ H ∧ ∀ (z : ℕ → L) (N : ℕ) (D : ℝ), 1 ≤ N → 0 ≤ D →
      (∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) →
      (∀ t < N, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D) →
      Nonempty (ActualWalkFrame b e z N D C H) := by
  classical
  obtain ⟨C, hC, hp⟩ := planarLatticeRectangle_packing b e
  obtain ⟨δ, hδ, hsep⟩ := planarEmbedding_positive_separation b e
  let H : ℝ := max 1 (1 / δ)
  have hH : 1 ≤ H := le_max_left _ _
  have hH0 : 0 ≤ H := by linarith
  have hHδ : 1 ≤ H * δ := (div_le_iff₀ hδ).mp (le_max_right _ _)
  refine ⟨C, H, hC, hH, ?_⟩
  intro z N D hN hD hinj hs
  obtain ⟨i, hi, j, hj, hdiam⟩ := walk_diameter_pair b e z N
  let r := dist (planarEmbedding b e (z i)) (planarEmbedding b e (z j))
  have hδr : δ ≤ r := by
    have hz : z 0 ≠ z 1 := by
      intro hz
      have he := hinj 0 (by omega) 1 hN hz
      omega
    have hlo := hsep (z 0 - z 1) (sub_ne_zero.mpr hz)
    rw [planarEmbedding_sub_signed, ← dist_eq_norm] at hlo
    exact hlo.trans (hdiam 0 (by omega) 1 hN)
  have hr : 0 < r := hδ.trans_le hδr
  let a := planarEmbedding b e (z j - z i)
  have hna : ‖a‖ = r := by
    simp only [a, r, planarEmbedding_sub_signed, ← dist_eq_norm, dist_comm]
  have ha : a ≠ 0 := by
    intro he
    rw [he, norm_zero] at hna
    linarith
  obtain ⟨o, ho0, ho1⟩ := exists_diameter_orientation a ha
  have ho0' : o a 0 = r := ho0.trans hna
  let c := planarEmbedding b e (z i)
  let R := max 1 r
  let W := walkTransverseWidth b e o z N i
  have hR : 1 ≤ R := le_max_left _ _
  have hW : 1 ≤ W := le_max_left _ _
  have hactual : ∀ t ≤ N, 0 ≤ (o (planarEmbedding b e (z t) - c)) 0 ∧
      (o (planarEmbedding b e (z t) - c)) 0 ≤ r ∧ |(o (planarEmbedding b e (z t) - c)) 1| ≤ r := by
    intro t ht
    have hv : ‖planarEmbedding b e (z t) - c‖ ≤ r := by
      simpa only [c, ← dist_eq_norm] using hdiam t ht i hi
    have hva : ‖(planarEmbedding b e (z t) - c) - a‖ ≤ r := by
      have he : (planarEmbedding b e (z t) - c) - a =
          planarEmbedding b e (z t) - planarEmbedding b e (z j) := by
        dsimp [c, a]
        rw [planarEmbedding_sub_signed]
        abel
      rw [he, ← dist_eq_norm]
      exact hdiam t ht j hj
    exact oriented_diameter_rectangle o ho0' ho1 hv hva
  have hWR : W ≤ R := by
    obtain ⟨k, hk, he⟩ := walkTransverseMax_attained b e o z N i
    have hl : walkTransverseMax b e o z N i ≤ r := by
      rw [he]
      simpa only [planarEmbedding_sub_signed] using (hactual k hk).2.2
    exact max_le_max le_rfl hl
  have hrect : ∀ x ∈ walkVertexSet z N, 0 ≤ (o (planarEmbedding b e x - c)) 0 ∧
      (o (planarEmbedding b e x - c)) 0 ≤ R ∧ |(o (planarEmbedding b e x - c)) 1| ≤ W := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have ht' : t ≤ N := by have h := Finset.mem_range.mp ht; omega
    have hw := walkTransverse_le_width b e o z ht' (i := i)
    exact ⟨(hactual t ht').1, (hactual t ht').2.1.trans (le_max_right _ _),
      by simpa only [c, planarEmbedding_sub_signed] using hw⟩
  have hpacking : (N + 1 : ℝ) ≤ C * R * W := by
    have hh := hp o c (walkVertexSet z N) R W hR hW hrect
    rw [walkVertexSet_card z N hinj] at hh
    exact_mod_cast hh
  have hstep : r ≤ D * N := bounded_walk_pair_distance b e z hi hj hD hs
  have hRmax : R ≤ max 1 (D * N) := max_le_max le_rfl hstep
  have hRHr : R ≤ H * r := by
    apply max_le
    · exact hHδ.trans (mul_le_mul_of_nonneg_left hδr hH0)
    · nlinarith
  have hRstep : R ≤ H * D * N := hRHr.trans (by
    have hh := mul_le_mul_of_nonneg_left hstep hH0
    simpa only [mul_assoc] using hh)
  have harea : R * W ≤ H^2 * D^2 * (N : ℝ)^2 := by
    calc
      R * W ≤ R * R := mul_le_mul_of_nonneg_left hWR (by linarith)
      _ ≤ (H * D * N) * (H * D * N) :=
        mul_le_mul hRstep hRstep (by linarith) (by positivity)
      _ = _ := by ring
  have hdiff0 := single_walk_many_differences_width b e o z hi hj hD hr hs hinj ho0' ho1
  have hdiff : R * W ≤ H *
      max 1 (max D ((planarLatticeBall b e (4 * D)).card * |planarCellDet e|)) *
        (latticeDifferences (walkVertexSet z N)).card := by
    calc
      R * W ≤ (H * r) * W := mul_le_mul_of_nonneg_right hRHr (by linarith)
      _ = H * (r * W) := by ring
      _ ≤ H * (max 1 (max D ((planarLatticeBall b e (4 * D)).card * |planarCellDet e|)) *
          (latticeDifferences (walkVertexSet z N)).card) := mul_le_mul_of_nonneg_left hdiff0 hH0
      _ = _ := by ring
  exact ⟨{
    orientation := o
    originIndex := i
    endpointIndex := j
    originIndex_le := hi
    endpointIndex_le := hj
    center := c
    center_eq := rfl
    diameter := r
    diameter_eq := rfl
    diameter_pos := hr
    diameter_maximal := hdiam
    length := R
    length_eq := rfl
    width := W
    width_eq := rfl
    endpoint_horizontal := ho0'
    endpoint_transverse_zero := ho1
    one_le_width := hW
    width_le_length := hWR
    rectangle := hrect
    difference_rectangle := lattice_differences_rectangle b e o c (walkVertexSet z N) hrect
    packing := hpacking
    diameter_step := hstep
    length_step_max := hRmax
    length_step := hRstep
    area_upper := harea
    area_differences := hdiff }⟩

/-- On the `D≥1` branch used by the proof schedule, the enlarged rectangle
length still obeys the exact actual-step bound `R≤DN`. -/
theorem ActualWalkFrame.length_step_of_one_le {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {z : ℕ → L} {N : ℕ} {D C H : ℝ}
    (f : ActualWalkFrame b e z N D C H) (hN : 1 ≤ N) (hD : 1 ≤ D) :
    f.length ≤ D * N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ D * N := by nlinarith
  exact f.length_step_max.trans (max_le hp le_rfl)


/-- The manuscript's exact area upper bound on the sufficient `D≥1` branch. -/
theorem ActualWalkFrame.area_upper_of_one_le {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {z : ℕ → L} {N : ℕ} {D C H : ℝ}
    (f : ActualWalkFrame b e z N D C H) (hN : 1 ≤ N) (hD : 1 ≤ D) :
    f.length * f.width ≤ D^2 * (N : ℝ)^2 := by
  have hR := f.length_step_of_one_le hN hD
  have hR0 : 0 ≤ f.length := zero_lt_one.le.trans (f.one_le_width.trans f.width_le_length)
  calc
    f.length * f.width ≤ f.length * f.length := mul_le_mul_of_nonneg_left f.width_le_length hR0
    _ ≤ (D * N) * (D * N) := mul_le_mul hR hR hR0 (by positivity)
    _ = _ := by ring

end Entry002
