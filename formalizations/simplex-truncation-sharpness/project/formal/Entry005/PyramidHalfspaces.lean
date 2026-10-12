import Entry005.FiniteHalfspaceCauchy
import Entry005.PyramidVolume

noncomputable section
open Metric MeasureTheory
open scoped RealInnerProductSpace Pointwise
namespace Entry005

def pyramidSlope (h : ℝ) : ℝ := Real.sqrt (1 + h ^ 2)

theorem pyramidSlope_pos (h : ℝ) : 0 < pyramidSlope h := by
  exact Real.sqrt_pos.mpr (by positivity)

theorem pyramidSlope_sq (h : ℝ) : pyramidSlope h ^ 2 = 1 + h ^ 2 :=
  Real.sq_sqrt (by positivity)

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pyramidBaseNormal : WithLp 2 (E × ℝ) := WithLp.toLp 2 ((0 : E), (-1 : ℝ))

def pyramidSideNormal (n : E) (h : ℝ) : WithLp 2 (E × ℝ) :=
  (pyramidSlope h)⁻¹ • WithLp.toLp 2 (n, h)

def pyramidHalfspaceNormal (n : ι → E) (h : ι → ℝ) : Option ι → WithLp 2 (E × ℝ)
  | none => pyramidBaseNormal
  | some i => pyramidSideNormal (n i) (h i)

def pyramidHalfspaceHeight (h : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => h i / pyramidSlope (h i)

omit [Fintype ι] [InnerProductSpace ℝ E] in
theorem pyramidBaseNormal_unit : ‖(pyramidBaseNormal : WithLp 2 (E × ℝ))‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(0 : E)‖ ^ 2 + ‖(-1 : ℝ)‖ ^ 2 = 1 ^ 2
  norm_num [pyramidBaseNormal]

omit [Fintype ι] in
theorem pyramidSideNormal_unit (n : E) (h : ℝ) (hn : ‖n‖ = 1) :
    ‖pyramidSideNormal n h‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [pyramidSideNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (pyramidSlope_pos h), mul_pow, inv_pow, WithLp.prod_norm_sq_eq_of_L2]
  change (pyramidSlope h ^ 2)⁻¹ * (‖n‖ ^ 2 + ‖h‖ ^ 2) = 1 ^ 2
  rw [hn, Real.norm_eq_abs, sq_abs, pyramidSlope_sq]
  have hp : 1 + h ^ 2 ≠ 0 := by positivity
  field_simp

omit [Fintype ι] in
theorem inner_pyramidBaseNormal (x : E) (t : ℝ) :
    inner ℝ pyramidBaseNormal (WithLp.toLp 2 (x, t)) = -t := by
  simp [pyramidBaseNormal, WithLp.prod_inner_apply]

omit [Fintype ι] in
theorem inner_pyramidSideNormal (n x : E) (h t : ℝ) :
    inner ℝ (pyramidSideNormal n h) (WithLp.toLp 2 (x, t)) =
      (inner ℝ n x + h * t) / pyramidSlope h := by
  simp [pyramidSideNormal, real_inner_smul_left, WithLp.prod_inner_apply, div_eq_mul_inv]
  ring

omit [Fintype ι] in
theorem mem_pyramidHalfspace_iff (n : ι → E) (h : ι → ℝ) (x : E) (t : ℝ) :
    WithLp.toLp 2 (x, t) ∈ finiteHalfspaceSet (pyramidHalfspaceNormal n h)
      (pyramidHalfspaceHeight h) ↔
      0 ≤ t ∧ ∀ i, inner ℝ (n i) x + h i * t ≤ h i := by
  constructor
  · intro hp
    have ht := hp none
    change inner ℝ pyramidBaseNormal (WithLp.toLp 2 (x, t)) ≤ 0 at ht
    rw [inner_pyramidBaseNormal] at ht
    refine ⟨by linarith, ?_⟩
    intro i
    have hi := hp (some i)
    change inner ℝ (pyramidSideNormal (n i) (h i)) (WithLp.toLp 2 (x, t)) ≤
      h i / pyramidSlope (h i) at hi
    rw [inner_pyramidSideNormal] at hi
    exact (div_le_div_iff_of_pos_right (pyramidSlope_pos _)).mp hi
  · rintro ⟨ht, hp⟩ (i | i)
    · change inner ℝ pyramidBaseNormal (WithLp.toLp 2 (x, t)) ≤ 0
      rw [inner_pyramidBaseNormal]
      linarith
    · change inner ℝ (pyramidSideNormal (n i) (h i)) (WithLp.toLp 2 (x, t)) ≤
        h i / pyramidSlope (h i)
      rw [inner_pyramidSideNormal]
      exact (div_le_div_iff_of_pos_right (pyramidSlope_pos _)).mpr (hp i)

omit [Fintype ι] in
theorem finite_halfspace_convex (n : ι → E) (h : ι → ℝ) :
    Convex ℝ (finiteHalfspaceSet n h) := by
  intro x hx y hy a b ha hb hab i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  calc
    a * inner ℝ (n i) x + b * inner ℝ (n i) y ≤ a * h i + b * h i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = h i := by rw [← add_mul, hab, one_mul]

omit [Fintype ι] in
/-- Actual compactness rules out every nonzero homogeneous recession direction. -/
theorem finite_halfspace_homogeneous_eq_zero (n : ι → E) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hc : IsCompact (finiteHalfspaceSet n h))
    (x : E) (hx : ∀ i, inner ℝ (n i) x ≤ 0) : x = 0 := by
  obtain ⟨R, hR⟩ := (hc.image continuous_norm).bddAbove
  have h0 : (0 : E) ∈ finiteHalfspaceSet n h := by simpa [finiteHalfspaceSet] using hh
  have hRn : 0 ≤ R := by simpa using hR ⟨0, h0, rfl⟩
  by_contra hx0
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let a := (R + 1) / ‖x‖
  have ha : 0 ≤ a := div_nonneg (by linarith) hn.le
  have hax : a • x ∈ finiteHalfspaceSet n h := by
    intro i
    rw [inner_smul_right]
    exact (mul_nonpos_of_nonneg_of_nonpos ha (hx i)).trans (hh i)
  have hb := hR ⟨a • x, hax, rfl⟩
  change ‖a • x‖ ≤ R at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at hb
  dsimp [a] at hb
  rw [div_mul_cancel₀ _ hn.ne'] at hb
  linarith

omit [Fintype ι] in
theorem pyramidHalfspaceNormal_unit (n : ι → E) (h : ι → ℝ) (hn : ∀ i, ‖n i‖ = 1)
    (i : Option ι) : ‖pyramidHalfspaceNormal n h i‖ = 1 := by
  cases i with
  | none => exact pyramidBaseNormal_unit
  | some i => exact pyramidSideNormal_unit (n i) (h i) (hn i)

omit [Fintype ι] in
theorem pyramidHalfspaceNormal_injective (n : ι → E) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hinj : Function.Injective n) :
    Function.Injective (pyramidHalfspaceNormal n h) := by
  have hbase : ∀ i, pyramidBaseNormal ≠ pyramidSideNormal (n i) (h i) := by
    intro i heq
    have hf := congrArg (fun p : WithLp 2 (E × ℝ) => ‖p.ofLp.1‖) heq
    change ‖(0 : E)‖ = ‖(pyramidSlope (h i))⁻¹ • n i‖ at hf
    rw [norm_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (pyramidSlope_pos _), hn i, mul_one] at hf
    exact (inv_ne_zero (pyramidSlope_pos _).ne') hf.symm
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (hbase j hij)
  | some i =>
    cases j with
    | none => exact False.elim (hbase i hij.symm)
    | some j =>
      have hf := congrArg (fun p : WithLp 2 (E × ℝ) => p.ofLp.1) hij
      change (pyramidSlope (h i))⁻¹ • n i = (pyramidSlope (h j))⁻¹ • n j at hf
      have hs := congrArg norm hf
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pyramidSlope_pos _),
        hn i, hn j, mul_one] at hs
      rw [← hs] at hf
      have he := smul_right_injective E (inv_ne_zero (pyramidSlope_pos (h i)).ne') hf
      exact congrArg some (hinj he)

section Representation
variable [Nontrivial E]

omit [Fintype ι] in
theorem finite_halfspace_index_nonempty (n : ι → E) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (hc : IsCompact (finiteHalfspaceSet n h)) : Nonempty ι := by
  classical
  by_contra hi
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  apply hx
  exact finite_halfspace_homogeneous_eq_zero n h hh hc x (fun i => False.elim (hi ⟨i⟩))

omit [Fintype ι] in
/-- Genuine finite-halfspace representation of the canonical convex pyramid.
Compactness, positive support heights and a nontrivial base space supply the
otherwise implicit top-height bound. Redundant halfspaces are allowed. -/
theorem pyramidSet_finite_halfspace (n : ι → E) (h : ι → ℝ)
    (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    pyramidSet (finiteHalfspaceSet n h) =
      finiteHalfspaceSet (pyramidHalfspaceNormal n h) (pyramidHalfspaceHeight h) := by
  have hconv := finite_halfspace_convex n h
  obtain ⟨i₀⟩ := finite_halfspace_index_nonempty n h (fun i => (hh i).le) hc
  ext p
  obtain ⟨⟨x, t⟩, rfl⟩ := WithLp.toLp_surjective 2 p
  rw [mem_pyramidHalfspace_iff, mem_pyramidSet_iff hconv]
  constructor
  · rintro (hp | ⟨r, hr, z, hz, hp⟩)
    · have hxt : (x, t) = ((0 : E), (1 : ℝ)) := congrArg WithLp.ofLp hp
      cases hxt
      refine ⟨by norm_num, ?_⟩
      intro i
      simp
    · have hxt : (x, t) = (r • z, 1 - r) := congrArg WithLp.ofLp hp
      cases hxt
      refine ⟨by linarith [hr.2], ?_⟩
      intro i
      rw [inner_smul_right]
      have hm := mul_le_mul_of_nonneg_left (hz i) hr.1
      nlinarith
  · rintro ⟨ht, hp⟩
    have htop : t ≤ 1 := by
      by_contra htop
      have ht' : 1 < t := lt_of_not_ge htop
      have hx : ∀ i, inner ℝ (n i) x ≤ 0 := by
        intro i
        have hm : h i < h i * t := lt_mul_of_one_lt_right (hh i) ht'
        linarith [hp i]
      have hx0 := finite_halfspace_homogeneous_eq_zero n h (fun i => (hh i).le) hc x hx
      have hpi := hp i₀
      rw [hx0, inner_zero_right, zero_add] at hpi
      have hm : h i₀ < h i₀ * t := lt_mul_of_one_lt_right (hh i₀) ht'
      linarith
    by_cases ht1 : t = 1
    · have hx0 : x = 0 := finite_halfspace_homogeneous_eq_zero n h
        (fun i => (hh i).le) hc x (by intro i; have hi := hp i; rw [ht1, mul_one] at hi; linarith)
      exact Or.inl (by simp [hx0, ht1, pyramidApex])
    · have hr : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne htop ht1)
      let z := (1 - t)⁻¹ • x
      have hz : z ∈ finiteHalfspaceSet n h := by
        intro i
        change inner ℝ (n i) ((1 - t)⁻¹ • x) ≤ h i
        rw [inner_smul_right]
        have hi : inner ℝ (n i) x ≤ h i * (1 - t) := by nlinarith [hp i]
        simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hr).mpr hi
      refine Or.inr ⟨1 - t, ⟨hr.le, by linarith⟩, z, hz, ?_⟩
      apply WithLp.ofLp_injective
      change (x, t) = ((1 - t) • ((1 - t)⁻¹ • x), 1 - (1 - t))
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      congr 1
      ring

end Representation
end Entry005
