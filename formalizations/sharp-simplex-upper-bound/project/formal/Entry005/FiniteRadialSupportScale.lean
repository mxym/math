import Entry005.ActualSupportFirstVariationTest
import Entry005.ProjectionVolumeSqueeze

/-! A direct volume estimate from the actual radial facet cones.
No mixed-volume, first-variation, or inverse-Minkowski theorem is used. -/

noncomputable section
open Metric MeasureTheory Module Function Filter
open scoped BigOperators RealInnerProductSpace Pointwise Topology
namespace Entry005

section FiniteCover
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem finite_halfspace_scaled_radial_cover
    (n : ι → E) (h s : ι → ℝ) (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : E) 1 ⊆ finiteHalfspaceSet n h)
    (hh : ∀ i, 0 < h i) (hs : ∀ i, 0 < s i)
    (P : Set E) (hP : ∀ x ∈ P, ∀ i, inner ℝ (n i) x ≤ s i * h i) :
    P ⊆ (⋃ i, s i • finiteHalfspaceFacetCone n h i) ∪ {0} := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inr hx0
  let a : ℝ := 1 / (‖x‖ + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hax : a • x ∈ finiteHalfspaceSet n h := by
    apply hb
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha]
    dsimp [a]
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith [norm_nonneg x])
  have hax0 : a • x ≠ 0 := smul_ne_zero ha.ne' hx0
  obtain ⟨i, t, ht, q, hq, heq⟩ :=
    finite_halfspace_nonzero_radial_cover n h hc (a • x) hax hax0
  have hxq : x = (t / a) • q := by
    have he := congrArg (fun z : E => a⁻¹ • z) heq
    simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul, div_eq_mul_inv,
      mul_comm] using he
  have hbound : t / a ≤ s i := by
    have hi := hP x hx i
    rw [hxq, inner_smul_right, hq.2] at hi
    exact (mul_le_mul_iff_left₀ (hh i)).mp hi
  have hr0 : 0 ≤ (t / a) / s i := div_nonneg (div_nonneg ht.1 ha.le) (hs i).le
  have hr1 : (t / a) / s i ≤ 1 := (div_le_one (hs i)).mpr hbound
  apply Or.inl
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  refine ⟨((t / a) / s i) • q, ⟨(t / a) / s i, ⟨hr0, hr1⟩, q, hq, rfl⟩, ?_⟩
  change s i • (((t / a) / s i) • q) = x
  have he : s i * ((t / a) / s i) = t / a := by field_simp [(hs i).ne']
  rw [smul_smul, he, ← hxq]

end FiniteCover

section FiniteVolume
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem finite_halfspace_scaled_radial_volume_bound
    (n : ι → E) (h s : ι → ℝ) (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : E) 1 ⊆ finiteHalfspaceSet n h)
    (hh : ∀ i, 0 < h i) (hs : ∀ i, 0 < s i)
    (P : Set E) (hP : ∀ x ∈ P, ∀ i, inner ℝ (n i) x ≤ s i * h i) :
    (volume P).toReal ≤ ∑ i, s i ^ finrank ℝ E *
      (volume (finiteHalfspaceFacetCone n h i)).toReal := by
  classical
  have hcones : ∀ i, IsCompact (s i • finiteHalfspaceFacetCone n h i) := by
    intro i
    exact (finite_halfspace_facet_cone_compact n h i hc).smul (s i)
  have hle : volume P ≤ ∑ i, volume (s i • finiteHalfspaceFacetCone n h i) := by
    calc
      volume P ≤ volume ((⋃ i, s i • finiteHalfspaceFacetCone n h i) ∪ {0}) :=
        measure_mono (finite_halfspace_scaled_radial_cover n h s hc hb hh hs P hP)
      _ ≤ volume (⋃ i, s i • finiteHalfspaceFacetCone n h i) + volume ({0} : Set E) :=
        measure_union_le _ _
      _ = volume (⋃ i, s i • finiteHalfspaceFacetCone n h i) := by simp
      _ ≤ ∑ i, volume (s i • finiteHalfspaceFacetCone n h i) :=
        measure_iUnion_fintype_le _ _
  have ht : (∑ i, volume (s i • finiteHalfspaceFacetCone n h i)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun i _ => (hcones i).measure_ne_top)
  have hr := ENNReal.toReal_mono ht hle
  rw [ENNReal.toReal_sum (fun i _ => (hcones i).measure_ne_top)] at hr
  calc
    _ ≤ ∑ i, (volume (s i • finiteHalfspaceFacetCone n h i)).toReal := hr
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      real_volume_nonnegative_smul _ _ (hs i).le)

end FiniteVolume

theorem power_minus_one_le_bounded_geometric_sum {d : ℕ} (hd : 1 ≤ d)
    {s M : ℝ} (hs : 1 ≤ s) (hsM : s ≤ M) :
    s ^ d ≤ 1 + (d : ℝ) * M ^ (d - 1) * (s - 1) := by
  have hM : 1 ≤ M := hs.trans hsM
  have hsum : ∑ k ∈ Finset.range d, s ^ k ≤ (d : ℝ) * M ^ (d - 1) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range d, M ^ (d - 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (pow_le_pow_left₀ (by linarith) hsM k).trans
          (pow_le_pow_right₀ hM (by have := Finset.mem_range.mp hk; omega))
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_right hsum (by linarith : 0 ≤ s - 1)
  rw [geom_sum_mul] at hm
  linarith

section FiniteSupportTest
variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

theorem finite_halfspace_radial_support_test_bound (hd : 1 ≤ d)
    (n : ι → Space d) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h))
    (hb : closedBall (0 : Space d) 1 ⊆ finiteHalfspaceSet n h)
    (hheight : ∀ i, 1 ≤ h i)
    (P : Set (Space d)) (hcP : IsCompact P) (hneP : P.Nonempty)
    (M : ℝ) (hM : 1 ≤ M) (hPM : P ⊆ closedBall (0 : Space d) M)
    (hlower : ∀ i, h i ≤ compactSupportHeight P (n i)) :
    (volume P).toReal / (volume (finiteHalfspaceSet n h)).toReal ≤
      1 + (d : ℝ) * M ^ (d - 1) *
        ((∫ x, compactSupportHeight P (WithLp.toLp 2 x) ∂finiteHalfspaceConeLaw n h) - 1) := by
  classical
  let s : ι → ℝ := fun i => compactSupportHeight P (n i) / h i
  let v : ι → ℝ := fun i => (volume (finiteHalfspaceFacetCone n h i)).toReal
  let V : ℝ := (volume (finiteHalfspaceSet n h)).toReal
  let C : ℝ := (d : ℝ) * M ^ (d - 1)
  have hs : ∀ i, 1 ≤ s i := fun i => (one_le_div (hh i)).mpr (hlower i)
  have hsM : ∀ i, s i ≤ M := by
    intro i
    obtain ⟨q, hq, heq⟩ := compact_support_height_attained P hcP hneP (n i)
    have hqM : ‖q‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hPM hq
    have hp : compactSupportHeight P (n i) ≤ M := by
      rw [← heq]
      exact (real_inner_le_norm _ _).trans (by simpa [hn i] using hqM)
    exact (div_le_iff₀ (hh i)).mpr (hp.trans (by nlinarith [hheight i]))
  have hcov : ∀ x ∈ P, ∀ i, inner ℝ (n i) x ≤ s i * h i := by
    intro x hx i
    dsimp [s]
    rw [div_mul_cancel₀ _ (hh i).ne']
    exact compact_support_height_bound P hcP hneP _ x hx
  have hv : ∀ i, 0 ≤ v i := fun _ => ENNReal.toReal_nonneg
  have hdim : finrank ℝ (Space d) = d := by simp [Space]
  have hVP : (volume P).toReal ≤ ∑ i, s i ^ d * v i := by
    simpa only [hdim] using finite_halfspace_scaled_radial_volume_bound
      n h s hc hb hh (fun i => lt_of_lt_of_le zero_lt_one (hs i)) P hcov
  have hmass : ∑ i, v i = V :=
    (finite_halfspace_volume_eq_sum_cone_volumes n h hn hh hinj hc).symm
  have hweighted : ∑ i, s i * v i =
      V * ∫ x, compactSupportHeight P (WithLp.toLp 2 x) ∂finiteHalfspaceConeLaw n h := by
    rw [finite_halfspace_support_height_test_integral n h hn hh hc P hcP hneP]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hV0 : V ≠ 0 := (finite_halfspace_volume_pos n h hn hh hc).ne'
    have heq : ∑ i, s i * v i =
        (∑ i, finiteHalfspaceFacetArea n h i * compactSupportHeight P (n i)) / (d : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [s, v]
      rw [finite_halfspace_facet_cone_volume n h i (hn i) (hh i) hc, hdim]
      field_simp [(hh i).ne']
    rw [heq, hdim]
    change _ = V * (_ / ((d : ℝ) * V))
    field_simp
  have hsum : (∑ i, s i ^ d * v i) ≤
      V + C * (V * (∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂finiteHalfspaceConeLaw n h) - V) := by
    calc
      _ ≤ ∑ i, (1 + C * (s i - 1)) * v i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (power_minus_one_le_bounded_geometric_sum hd (hs i) (hsM i)) (hv i)
      _ = (∑ i, v i) + C * ((∑ i, s i * v i) - ∑ i, v i) := by
        simp only [add_mul, one_mul, Finset.sum_add_distrib]
        congr 1
        calc
          _ = ∑ i, C * (s i * v i - v i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by rw [hmass, hweighted]
  apply (div_le_iff₀ (finite_halfspace_volume_pos n h hn hh hc)).mpr
  dsimp [C, V] at hVP hsum ⊢
  nlinarith [hVP.trans hsum]

end FiniteSupportTest

section ActualSupportTest
variable {d : ℕ} [Nontrivial (Space d)]

theorem actual_body_volume_ratio_le_linear_support_test (hd : 1 ≤ d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hKP : K ⊆ P)
    (M : ℝ) (hM : 1 ≤ M) (hPM : P ⊆ closedBall (0 : Space d) M) :
    (volume P).toReal / (volume K).toReal ≤
      1 + (d : ℝ) * M ^ (d - 1) *
        ((∫ x, compactSupportHeight P (WithLp.toLp 2 x)
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) - 1) := by
  have hneK : K.Nonempty := ⟨0, hb (by simp)⟩
  have hneP : P.Nonempty := ⟨0, hKP (hb (by simp))⟩
  have hvol := (halfspace_approximation_volume_tendsto K hc hconv hb).comp hφ.tendsto_atTop
  have hratio := (tendsto_const_nhds (x := (volume P).toReal) (f := atTop)).div hvol
    (compact_body_volume_pos_of_unit_ball K hc hb).ne'
  have hi := actual_body_support_height_test_integral_tendsto K hc hconv hb μ φ hlim P hcP hneP
  have htest := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := (d : ℝ) * M ^ (d - 1))).mul
      (hi.sub (tendsto_const_nhds (x := (1 : ℝ)))))
  apply le_of_tendsto_of_tendsto' hratio htest
  intro k
  exact finite_halfspace_radial_support_test_bound hd _ _
    (halfspace_approximation_normals_unit K hc hconv hb (φ k))
    (halfspace_approximation_heights_pos K hc hconv hb (φ k))
    (halfspace_approximation_normals_injective K hc hconv hb (φ k))
    (halfspace_approximation_body_compact K hc hconv hb (φ k))
    (halfspace_approximation_body_contains_unit_ball K hc hconv hb (φ k))
    (fun i => compact_support_height_unit_ball K hc hneK hb (i : Space d)
      (halfspace_approximation_normals_unit K hc hconv hb (φ k) i))
    P hcP hneP M hM hPM
    (fun i => compact_support_height_mono K P hc hneK hcP hneP hKP (i : Space d))

theorem actual_body_same_assignment_linear_volume_bound {n : ℕ} (hd : 1 ≤ d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ))
    (P : Set (Space d)) (hcP : IsCompact P) (hKP : K ⊆ P)
    (M : ℝ) (hM : 1 ≤ M) (hPM : P ⊆ closedBall (0 : Space d) M)
    (w : Fin (n + 1) → Fin d → ℝ)
    (hw : ∀ i, compactSupportHeight P (WithLp.toLp 2 (w i)) = 1)
    (r : (Fin d → ℝ) → Fin (n + 1)) (hr : Measurable r) :
    (volume P).toReal / (volume K).toReal ≤
      1 + (d : ℝ) * M ^ d * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := by
  have ht := (actual_body_enclosing_support_height_assignment_test_bound K hb μ P hcP
    hKP M (by linarith) hPM w hw r hr).2.2
  have hv := actual_body_volume_ratio_le_linear_support_test hd K hc hconv hb μ φ hφ hlim
    P hcP hKP M hM hPM
  have hc0 : 0 ≤ (d : ℝ) * M ^ (d - 1) := by positivity
  have he := mul_le_mul_of_nonneg_left (sub_le_sub_right ht 1) hc0
  have hp : M ^ (d - 1) * M = M ^ d := by rw [← pow_succ]; congr 1; omega
  have he' : (d : ℝ) * M ^ (d - 1) *
      ((∫ x, compactSupportHeight P (WithLp.toLp 2 x)
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) - 1) ≤
      (d : ℝ) * M ^ d * ∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
        ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)) := by
    calc
      _ ≤ (d : ℝ) * M ^ (d - 1) * (M * ∫ x,
          ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (r x))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) := by linarith [he]
      _ = _ := by rw [← hp]; ring
  linarith

end ActualSupportTest

end Entry005
