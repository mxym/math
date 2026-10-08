import Entry002.GenericWalkExtraction
import Entry002.TinySteps

/-! Rectangle packing for the actual full lattice and arbitrary planar
orientation. The packing scale is derived from proved positive separation. -/
set_option autoImplicit false
namespace Entry002
open Module
variable {L : Type*} [AddCommGroup L]

noncomputable def planarLatticePixel (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane)
    (a : ℝ) (z : L) : ℤ × ℤ :=
  (⌊a * (o (planarEmbedding b e z - c)) 0⌋,
    ⌊a * (o (planarEmbedding b e z - c)) 1⌋)

/-- A genuine lattice separation scale makes the coordinate pixel injective. -/
theorem planarLatticePixel_injective (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane)
    {a : ℝ} (ha : 0 < a)
    (hsep : ∀ x y : L, x ≠ y → 2 ≤ a * dist (planarEmbedding b e x) (planarEmbedding b e y)) :
    Function.Injective (planarLatticePixel b e o c a) := by
  intro x y h
  have hr := congrArg Prod.fst h
  have hi := congrArg Prod.snd h
  have hfloor {u v : ℝ} (hh : ⌊a * u⌋ = ⌊a * v⌋) : a * |u - v| < 1 := by
    have h1 := Int.floor_le (a * u)
    have h2 := Int.lt_floor_add_one (a * u)
    have h3 := Int.floor_le (a * v)
    have h4 := Int.lt_floor_add_one (a * v)
    rw [hh] at h1 h2
    have hlt : |a * (u - v)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa only [abs_mul, abs_of_pos ha] using hlt
  have hr' := hfloor hr
  have hi' := hfloor hi
  let q := o (planarEmbedding b e x - c) - o (planarEmbedding b e y - c)
  have hn : ‖q‖ ≤ |q 0| + |q 1| := by
    simpa only [planeComplex_re, planeComplex_im, planeComplex.norm_map] using
      Complex.norm_le_abs_re_add_abs_im (planeComplex q)
  have hnorm : a * ‖q‖ < 2 := by
    have hn' := mul_le_mul_of_nonneg_left hn ha.le
    dsimp [planarLatticePixel] at hr' hi'
    dsimp [q] at hn'
    simp only [mul_add] at hn'
    linarith
  have he : q = o (planarEmbedding b e x - planarEmbedding b e y) := by
    dsimp [q]
    rw [← map_sub]
    congr 1
    abel
  rw [he, o.norm_map, ← dist_eq_norm] at hnorm
  by_contra hne
  exact (not_lt_of_ge (hsep x y hne)) hnorm

/-- Pixel counting in an arbitrary oriented rectangle. -/
theorem planarLatticeRectangle_card_at_scale (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane)
    (E : Finset L) {a R W : ℝ} (ha : 2 ≤ a) (hR : 1 ≤ R) (hW : 1 ≤ W)
    (hsep : ∀ x y : L, x ≠ y → 2 ≤ a * dist (planarEmbedding b e x) (planarEmbedding b e y))
    (hE : ∀ z ∈ E, 0 ≤ (o (planarEmbedding b e z - c)) 0 ∧
      (o (planarEmbedding b e z - c)) 0 ≤ R ∧ |(o (planarEmbedding b e z - c)) 1| ≤ W) :
    (E.card : ℝ) ≤ 2 * (a + 1)^2 * R * W := by
  classical
  have ha0 : 0 < a := by linarith
  let B : Finset (ℤ × ℤ) := Finset.Icc 0 ⌊a * R⌋ ×ˢ Finset.Icc ⌊-a * W⌋ ⌊a * W⌋
  have hb : E.image (planarLatticePixel b e o c a) ⊆ B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hz0, hzR, hzW⟩ := hE z hz
    have hzw := abs_le.mp hzW
    simp only [B, Finset.mem_product, Finset.mem_Icc, planarLatticePixel]
    refine ⟨⟨Int.floor_nonneg.mpr (mul_nonneg ha0.le hz0),
      Int.floor_mono (mul_le_mul_of_nonneg_left hzR ha0.le)⟩, ⟨?_, ?_⟩⟩
    · apply Int.floor_mono
      nlinarith [mul_le_mul_of_nonneg_left hzw.1 ha0.le]
    · exact Int.floor_mono (mul_le_mul_of_nonneg_left hzw.2 ha0.le)
  have hcard : E.card ≤ B.card := by
    rw [← Finset.card_image_iff.mpr (planarLatticePixel_injective b e o c ha0 hsep).injOn]
    exact Finset.card_le_card hb
  have hR0 : (0 : ℤ) ≤ ⌊a * R⌋ + 1 := by
    have hh : (0 : ℤ) ≤ ⌊a * R⌋ := Int.floor_nonneg.mpr (by positivity)
    omega
  have hW0 : ⌊-a * W⌋ ≤ ⌊a * W⌋ + 1 := by
    have hh : ⌊-a * W⌋ ≤ ⌊a * W⌋ := Int.floor_mono (by nlinarith)
    omega
  have hcr : ((Finset.Icc (0 : ℤ) ⌊a * R⌋).card : ℝ) = (⌊a * R⌋ : ℝ) + 1 := by
    have h := Int.card_Icc_of_le 0 ⌊a * R⌋ hR0
    simp only [sub_zero] at h
    exact_mod_cast h
  have hcw : ((Finset.Icc ⌊-a * W⌋ ⌊a * W⌋).card : ℝ) =
      (⌊a * W⌋ : ℝ) + 1 - (⌊-a * W⌋ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌊-a * W⌋ ⌊a * W⌋ hW0
  have hrb : ((Finset.Icc (0 : ℤ) ⌊a * R⌋).card : ℝ) ≤ (a + 1) * R := by
    rw [hcr]
    nlinarith [Int.floor_le (a * R)]
  have hwb : ((Finset.Icc ⌊-a * W⌋ ⌊a * W⌋).card : ℝ) ≤ (2 * a + 2) * W := by
    rw [hcw]
    nlinarith [Int.floor_le (a * W), Int.lt_floor_add_one (-a * W)]
  have hh : (E.card : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊a * R⌋).card : ℝ) *
      ((Finset.Icc ⌊-a * W⌋ ⌊a * W⌋).card : ℝ) := by
    dsimp only [B] at hcard
    rw [Finset.card_product] at hcard
    exact_mod_cast hcard
  calc
    _ ≤ _ := hh
    _ ≤ ((a + 1) * R) * ((2 * a + 2) * W) :=
      mul_le_mul hrb hwb (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Rectangle packing for every full planar lattice, with a constant derived
from its actual proved minimum separation. -/
theorem planarLatticeRectangle_packing (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane) (E : Finset L)
      (R W : ℝ), 1 ≤ R → 1 ≤ W →
      (∀ z ∈ E, 0 ≤ (o (planarEmbedding b e z - c)) 0 ∧
        (o (planarEmbedding b e z - c)) 0 ≤ R ∧ |(o (planarEmbedding b e z - c)) 1| ≤ W) →
      (E.card : ℝ) ≤ C * R * W := by
  obtain ⟨δ, hδ, hsepδ⟩ := planarEmbedding_positive_separation b e
  let a : ℝ := max 2 (2 / δ)
  have ha : 2 ≤ a := le_max_left _ _
  have hsep : ∀ x y : L, x ≠ y → 2 ≤ a * dist (planarEmbedding b e x) (planarEmbedding b e y) := by
    intro x y hxy
    have hd : δ ≤ dist (planarEmbedding b e x) (planarEmbedding b e y) := by
      simpa only [planarEmbedding_sub_signed, dist_eq_norm] using hsepδ (x - y) (sub_ne_zero.mpr hxy)
    have hle : 2 / δ ≤ a := le_max_right _ _
    have hmul : 2 ≤ a * δ := (div_le_iff₀ hδ).mp hle
    exact hmul.trans (mul_le_mul_of_nonneg_left hd (by linarith))
  refine ⟨2 * (a + 1)^2, by positivity, ?_⟩
  intro o c E R W hR hW hE
  exact planarLatticeRectangle_card_at_scale b e o c E ha hR hW hsep hE


/-- The manuscript packing bound for an actual self-avoiding walk contained
in a rectangle; the constant depends only on the actual full lattice. -/
theorem self_avoiding_walk_rectangle_packing (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o : Plane ≃ₗᵢ[ℝ] Plane) (c : Plane) (z : ℕ → L)
      (N : ℕ) (R W : ℝ), 1 ≤ R → 1 ≤ W →
      (∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) →
      (∀ t ≤ N, 0 ≤ (o (planarEmbedding b e (z t) - c)) 0 ∧
        (o (planarEmbedding b e (z t) - c)) 0 ≤ R ∧
        |(o (planarEmbedding b e (z t) - c)) 1| ≤ W) →
      (N + 1 : ℝ) ≤ C * R * W := by
  obtain ⟨C, hC, hp⟩ := planarLatticeRectangle_packing b e
  refine ⟨C, hC, ?_⟩
  intro o c z N R W hR hW hinj hE
  have h := hp o c (walkVertexSet z N) R W hR hW (by
    intro x hx
    classical
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact hE t (by have hh := Finset.mem_range.mp ht; omega))
  rw [walkVertexSet_card z N hinj] at h
  exact_mod_cast h


/-- Actual metric balls have quadratic cardinality growth in every full planar
lattice. The constant is obtained from the proved rectangle packing theorem. -/
theorem planarLatticeBall_quadratic_card (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → (planarLatticeBall b e R).card ≤ C * R^2 := by
  obtain ⟨C, hC, hp⟩ := planarLatticeRectangle_packing b e
  refine ⟨2 * C, by positivity, ?_⟩
  intro R hR
  let c : Plane := EuclideanSpace.single 0 (-R)
  have h := hp (LinearIsometryEquiv.refl ℝ Plane) c (planarLatticeBall b e R) (2 * R) R
    (by linarith) hR (by
      intro x hx
      have hnorm := (mem_planarLatticeBall b e R x).mp hx
      have hr := (Complex.abs_re_le_norm (planeComplex (planarEmbedding b e x))).trans
        (by simpa only [planeComplex.norm_map] using hnorm)
      have hi := (Complex.abs_im_le_norm (planeComplex (planarEmbedding b e x))).trans
        (by simpa only [planeComplex.norm_map] using hnorm)
      simp only [planeComplex_re, planeComplex_im] at hr hi
      have hr' := abs_le.mp hr
      change 0 ≤ (planarEmbedding b e x - c) 0 ∧
        (planarEmbedding b e x - c) 0 ≤ 2 * R ∧ |(planarEmbedding b e x - c) 1| ≤ R
      simp only [c, PiLp.sub_apply, PiLp.single_apply, Fin.isValue, ↓reduceIte,
        sub_neg_eq_add]
      exact ⟨by linarith, by linarith, by simpa using hi⟩)
  nlinarith

/-- Logarithmic cardinality growth for the actual displacement alphabet. -/
theorem planarLatticeBall_log_card (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      Real.log (planarLatticeBall b e R).card ≤ Real.log C + 2 * Real.log R := by
  obtain ⟨C, hC, hb⟩ := planarLatticeBall_quadratic_card b e
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hpos : (0 : ℝ) < (planarLatticeBall b e R).card := by
    have hmem : (0 : L) ∈ planarLatticeBall b e R := by
      rw [mem_planarLatticeBall, planarEmbedding_zero, norm_zero]
      linarith
    exact_mod_cast Finset.card_pos.mpr ⟨0, hmem⟩
  have hr : 0 < R := by linarith
  have h := Real.log_le_log hpos (hb R hR)
  rw [Real.log_mul hC.ne' (pow_pos hr 2).ne', Real.log_pow] at h
  simpa only [Nat.cast_ofNat] using h

end Entry002
