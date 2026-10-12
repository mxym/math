import Entry002.GenericGeometricEnrichment

/-! Actual numerical construction of geometric enrichment margins.
Adapted from pinned OpenAI family028 MultiscaleSchedule.lean lines212--322.
All geometry constants and displacement alphabets come from the actual lattice.
-/
set_option autoImplicit false
namespace Entry002
open Module
open OAI.GaussianMoat
open WalkFreshEntropy
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- The two existing genuine metric-ball constructions denote the same set. -/
theorem wordStepBall_eq_planarLatticeBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (R : ℝ) :
    wordStepBall b e R = planarLatticeBall b e R := by
  ext x
  simp only [mem_wordStepBall, mem_planarLatticeBall]

noncomputable def displacementPackingConstant (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : ℝ := (planarLatticeBall_log_card b e).choose

theorem displacementPackingConstant_spec (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    0 < displacementPackingConstant b e ∧ ∀ R : ℝ, 1 ≤ R →
      Real.log (wordStepBall b e R).card ≤
        Real.log (displacementPackingConstant b e) + 2 * Real.log R := by
  have hh := (planarLatticeBall_log_card b e).choose_spec
  refine ⟨hh.1, ?_⟩
  intro R hR
  rw [wordStepBall_eq_planarLatticeBall]
  exact hh.2 R hR

lemma geometric_log_floor_exp {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ⌊Real.exp x⌋₊ ∧ x-1 ≤ Real.log (⌊Real.exp x⌋₊:ℝ) ∧
      Real.log (⌊Real.exp x⌋₊:ℝ) ≤ x := by
  have he : 2 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hn : 1 ≤ ⌊Real.exp x⌋₊ := Nat.floor_pos.mpr (by linarith only [he])
  have hnp : (0:ℝ)<⌊Real.exp x⌋₊ := by exact_mod_cast hn
  have hlow : Real.exp x/2 ≤ (⌊Real.exp x⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp x)
    linarith only [he,h]
  have hlo := Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num : (0:ℝ)<2)) hlow
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num : (2:ℝ)≠0),Real.log_exp] at hlo
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [h]
  have hhi := Real.log_le_log hnp (Nat.floor_le (Real.exp_nonneg x))
  rw [Real.log_exp] at hhi
  exact ⟨hn,by linarith only [hlo,hl2],hhi⟩

/-- Floors of the actual geometric scale produce every enrichment margin;
none of the GeometricFreshScale fields are presumed as a result certificate. -/
theorem geometric_fresh_scale_from_scale (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ) {D U g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200)
    (hL : 1 ≤ FreshEntropy.batchMeanLog S) (hU : 0 < U)
    (hlog : 2*(1+max 0 (Real.log (walkPackingConstant b e))) ≤ g*U)
    (hlarge : 640*FreshEntropy.batchMeanLog S ≤ g^5*U)
    (hsize : Real.log (16*geometricScale data hArith) +
      Real.log (walkFrameFactor b e *
        max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) ≤ g^2*U)
    (hdisp : 4*Real.log D+2*Real.log (displacementPackingConstant b e) ≤ 4*g*U)
    (hgeom : 2*Real.log (16*geometricScale data hArith)+4*Real.log D ≤ U/4)
    (hcap : ⌊U/FreshEntropy.batchMeanLog S⌋₊ ≤ S.card) :
    let μ := FreshEntropy.batchMeanLog S
    let n := ⌊Real.exp (g*U)⌋₊
    let q := ⌊U/μ⌋₊
    let m := ⌊g^2*U/μ⌋₊
    0<m ∧ m<q ∧ q≤S.card ∧ (m:ℝ)≤(2*g)*q ∧
      GeometricFreshScale data b e hArith S D (2*g) n m ∧
      2*Real.log (wordStepBall b e (D*n)).card≤8*(2*g)*q*μ := by
  let L := FreshEntropy.batchMeanLog S
  let n := ⌊Real.exp (g*U)⌋₊
  let q := ⌊U/L⌋₊
  let m := ⌊g^2*U/L⌋₊
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hg_le : g ≤ 1 := by linarith only [hg1]
  have hg2 : g^2 ≤ 1 := pow_le_one₀ hg.le hg_le
  have hg3 : g^3 ≤ 1 := pow_le_one₀ hg.le hg_le
  have h52 : g^5*U ≤ g^2*U := by
    have hpow : g^5=g^2*g^3 := by ring
    rw [hpow]
    nlinarith only [hg3,mul_nonneg (sq_nonneg g) hU.le]
  have h2U : g^2*U ≤ U := by nlinarith only [hg2,hU]
  have hLU : L ≤ U/2 := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,h2U,hLp]
  have hbL : L ≤ g^2*U := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,hLp]
  have he2 : 2 ≤ g*U := by
    have hh := le_max_left (0:ℝ) (Real.log (walkPackingConstant b e))
    linarith only [hh,hlog]
  obtain ⟨hn,hnlo,hnhi⟩ := geometric_log_floor_exp he2
  have hnlo' : g*U/2 ≤ Real.log n-Real.log (walkPackingConstant b e) := by
    change g*U-1 ≤ Real.log n at hnlo
    linarith only [hnlo,hlog,le_max_right (0:ℝ) (Real.log (walkPackingConstant b e))]
  have hu : 0 < Real.log n-Real.log (walkPackingConstant b e) :=
    lt_of_lt_of_le (div_pos (mul_pos hg hU) (by norm_num)) hnlo'
  have hqL : U-L ≤ (q:ℝ)*L := by
    have hf := Nat.lt_floor_add_one (U/L)
    have hm := mul_lt_mul_of_pos_right hf hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    linarith only [hm]
  have hqU : U/2 ≤ (q:ℝ)*L := by linarith only [hqL,hLU]
  have hqpos : 0 < q := by
    have : (0:ℝ)<q := by nlinarith only [hqU,hU,hLp]
    exact_mod_cast this
  have hbpos : 0 < m := by
    apply Nat.floor_pos.mpr
    exact (le_div_iff₀ hLp).mpr (by simpa only [one_mul] using hbL)
  have hbup : (m:ℝ)*L ≤ g^2*U := by
    exact (le_div_iff₀ hLp).mp (Nat.floor_le (by positivity : 0 ≤ g^2*U/L))
  have hratio : (m:ℝ) ≤ (2*g)*q := by
    have h1 := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 2*g by positivity)
    have h2 : g^2*U ≤ g*U := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg_le hg.le) hU.le
      simpa only [mul_one,pow_two] using hh
    apply (mul_le_mul_iff_left₀ hLp).mp
    nlinarith only [hbup,h1,h2]
  have hbq : m < q := by
    have hqr : (0:ℝ)<q := by exact_mod_cast hqpos
    have : (m:ℝ)<q := by nlinarith only [hratio,hg1,hqr]
    exact_mod_cast this
  refine ⟨hbpos,hbq,hcap,hratio,⟨hn,hu,?_,?_,?_,?_,?_⟩,?_⟩
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    dsimp only [L] at hbL
    nlinarith only [hbL,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ (2*g)^4 by positivity)
    nlinarith only [hlarge,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    change (m:ℝ)*L ≤ _
    nlinarith only [hbup,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    linarith only [hsize,hm]
  · have hqcap : (q:ℝ)*L ≤ S.card*L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) hLp.le
    have hgU := mul_le_mul_of_nonneg_right hg1 hU.le
    change 2*(2*Real.log n+Real.log (16*geometricScale data hArith)+2*Real.log D) ≤ S.card*L
    change Real.log n ≤ g*U at hnhi
    nlinarith only [hnhi,hgeom,hqU,hqcap,hgU,hU]
  · have hDn : 1 ≤ D*(n:ℝ) := by
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith only [hD,hn']
    have hh := (displacementPackingConstant_spec b e).2 (D*n) hDn
    have hDp : D ≠ 0 := by linarith only [hD]
    have hnp : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
    rw [Real.log_mul hDp hnp] at hh
    have hm := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 16*g by positivity)
    change Real.log n ≤ g*U at hnhi
    change 2*Real.log (wordStepBall b e (D*n)).card ≤ 8*(2*g)*q*L
    nlinarith only [hh,hnhi,hdisp,hm]


/-- The fixed lattice guards hold eventually, uniformly over every actual
batch whose mean and capacity obey the displayed numerical bounds. -/
theorem eventually_uniform_geometric_fresh_scales (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) {D g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200) :
    ∀ᶠ U : ℝ in Filter.atTop, ∀ (S : Finset ℕ) (X : ℝ),
      1 ≤ FreshEntropy.batchMeanLog S → FreshEntropy.batchMeanLog S ≤ 2*X →
      1280*X ≤ g^5*U → ⌊U/FreshEntropy.batchMeanLog S⌋₊ ≤ S.card →
      let μ := FreshEntropy.batchMeanLog S
      let n := ⌊Real.exp (g*U)⌋₊
      let q := ⌊U/μ⌋₊
      let m := ⌊g^2*U/μ⌋₊
      0<m ∧ m<q ∧ q≤S.card ∧ (m:ℝ)≤(2*g)*q ∧
        GeometricFreshScale data b e hArith S D (2*g) n m ∧
        2*Real.log (wordStepBall b e (D*n)).card≤8*(2*g)*q*μ := by
  let size := Real.log (16*geometricScale data hArith) +
    Real.log (walkFrameFactor b e *
      max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|)))
  let disp := 4*Real.log D+2*Real.log (displacementPackingConstant b e)
  let geom := 2*Real.log (16*geometricScale data hArith)+4*Real.log D
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((2*(1+max 0 (Real.log (walkPackingConstant b e))))/g),
    Filter.eventually_ge_atTop (size/g^2), Filter.eventually_ge_atTop (disp/(4*g)),
    Filter.eventually_ge_atTop (4*geom)] with U hU hlog hsize hdisp hgeom
  intro S X hmean hmeanup hrelative hcap
  apply geometric_fresh_scale_from_scale data b e hArith S (U := U) hD hg hg1 hmean
    (by linarith only [hU])
    (by simpa only [mul_comm] using (div_le_iff₀ hg).mp hlog)
    (by nlinarith only [hmeanup,hrelative])
    (by simpa only [size,mul_comm] using (div_le_iff₀ (sq_pos_of_pos hg)).mp hsize)
    (by simpa only [disp,mul_comm] using (div_le_iff₀ (mul_pos (by norm_num) hg)).mp hdisp)
    (by dsimp only [geom] at hgeom; linarith only [hgeom]) hcap

/-- A fixed lattice constant controlling every geometric guard. Its dependence
on the varying band parameter is entirely through the factor `g⁻²`. -/
noncomputable def geometricGuardConstant (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (D : ℝ) : ℝ :=
  max 1 (max (2*(1+max 0 (Real.log (walkPackingConstant b e))))
    (max (Real.log (16*geometricScale data hArith) +
      Real.log (walkFrameFactor b e *
        max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))))
      (max ((4*Real.log D+2*Real.log (displacementPackingConstant b e))/4)
        (4*(2*Real.log (16*geometricScale data hArith)+4*Real.log D)))))

theorem geometricGuardConstant_one_le (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (D : ℝ) :
    1 ≤ geometricGuardConstant data b e hArith D := le_max_left _ _

/-- Explicit uniform construction, valid even when `g` varies. The only fixed
lattice threshold is `geometricGuardConstant / g²`. All fresh-information and
displacement margins are proved from these scalar bounds. -/
theorem uniform_geometric_fresh_scales_of_guard (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ) {D g U X : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200)
    (hguard : geometricGuardConstant data b e hArith D ≤ g^2*U)
    (hmean : 1 ≤ FreshEntropy.batchMeanLog S)
    (hmeanup : FreshEntropy.batchMeanLog S ≤ 2*X)
    (hrelative : 1280*X ≤ g^5*U)
    (hcap : ⌊U/FreshEntropy.batchMeanLog S⌋₊ ≤ S.card) :
    let μ := FreshEntropy.batchMeanLog S
    let n := ⌊Real.exp (g*U)⌋₊
    let q := ⌊U/μ⌋₊
    let m := ⌊g^2*U/μ⌋₊
    0<m ∧ m<q ∧ q≤S.card ∧ (m:ℝ)≤(2*g)*q ∧
      GeometricFreshScale data b e hArith S D (2*g) n m ∧
      2*Real.log (wordStepBall b e (D*n)).card≤8*(2*g)*q*μ := by
  have hK := geometricGuardConstant_one_le data b e hArith D
  have hU : 0 < U := by nlinarith only [hK,hguard,sq_nonneg g]
  have hg_le : g ≤ 1 := by linarith only [hg1]
  have h2g : g^2*U ≤ g*U := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg_le hg.le) hU.le
    simpa only [mul_one,pow_two] using hh
  have h2U : g^2*U ≤ U := by
    have hp := pow_le_one₀ hg.le hg_le (n := 2)
    nlinarith only [hp,hU]
  have hguards := hguard
  unfold geometricGuardConstant at hguards
  have hfixed := (le_max_right _ _).trans hguards
  have hlog := (le_max_left _ _).trans hfixed
  have hrest := (le_max_right _ _).trans hfixed
  have hsize := (le_max_left _ _).trans hrest
  have hrest' := (le_max_right _ _).trans hrest
  have hdisp := (le_max_left _ _).trans hrest'
  have hgeom := (le_max_right _ _).trans hrest'
  apply geometric_fresh_scale_from_scale data b e hArith S (U := U)
    hD hg hg1 hmean hU
    (hlog.trans h2g)
    (by nlinarith only [hmeanup,hrelative])
    hsize
    (by linarith only [hdisp,hguard,h2g])
    (by linarith only [hgeom,hguard,h2U]) hcap

end Entry002
