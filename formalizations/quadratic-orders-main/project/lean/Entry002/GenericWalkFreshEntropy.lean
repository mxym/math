import Entry002.GenericFreshEntropy
import Entry002.GenericTimeKernels
import Entry002.GenericWalkFrame

/-! Fresh signed-residue entropy for the genuine uniform walk displacement law.
The transfer and scalar synthesis follow the pinned OpenAI family028
PointEnrichment.lean; geometry is the actual lattice frame and true planar norm.
-/
namespace Entry002.WalkFreshEntropy
open Module
open OAI.GaussianMoat
open Entry002.SignSeparation
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- Exact transfer from uniform actual displacements to their chosen genuine
walk endpoint representatives. -/
theorem differenceLaw_fresh (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (z : ℕ → L) (n : ℕ)
    {m r : ℕ} (hmr : m < r) (hr : r ≤ S.card)
    (o : Plane ≃ₗᵢ[ℝ] Plane) {T R W d δ : ℝ} (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log ((max (2 / |planarCellDet e|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤
      (1-d)*(r*FreshEntropy.batchMeanLog S-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ latticeDifferences (walkVertices z n),
      ∀ y ∈ latticeDifferences (walkVertices z n),
      x-y ∈ latticeRectangle b e o R W) :
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*
        Real.log (latticeDifferences (walkVertices z n)).card-2*m*Real.log (2*T) ≤
      (r-m : ℕ)*signedFreshCoordinate data S (walkDifferenceLaw z n)
        (fun ij => z ij.1.val) (fun ij => z ij.2.val) m (by omega) := by
  let Δ := latticeDifferences (walkVertices z n)
  let hne := walkDifferences_nonempty z n
  let := hne.to_subtype
  let X : Δ → L := fun ω => z (walkDifferenceRepresentative z n ω).1.val
  let Y : Δ → L := fun ω => z (walkDifferenceRepresentative z n ω).2.val
  have hXY : ∀ ω, X ω-Y ω=ω := walkDifferenceRepresentative_spec z n
  have h := FreshEntropy.actual_fresh_coordinate_entropy data b e hArith S hS hmr hr
    Δ hne X Y hXY o hT hpT hW hWR hd hd1 hδ
    hgap hlarge hΔ
  change _ ≤ (r-m : ℕ)*signedFreshCoordinate data S
    ((FinLaw.uniform Δ).map (walkDifferenceRepresentative z n))
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) m (by omega)
  rw [signedFreshCoordinate_map]
  exact h

/-- Subtraction doubles the actual oriented coordinate bounds. -/
theorem latticeRectangle_sub (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (o : Plane ≃ₗᵢ[ℝ] Plane) {R W : ℝ}
    {x y : L} (hx : x ∈ latticeRectangle b e o R W)
    (hy : y ∈ latticeRectangle b e o R W) :
    x-y ∈ latticeRectangle b e o (2*R) (2*W) := by
  change |o (planarEmbedding b e (x-y)) 0| ≤ 2*R ∧
    |o (planarEmbedding b e (x-y)) 1| ≤ 2*W
  rw [planarEmbedding_sub_signed, map_sub]
  simp only [PiLp.sub_apply]
  exact ⟨(abs_sub _ _).trans (by linarith [hx.1,hy.1]),
    (abs_sub _ _).trans (by linarith [hx.2,hy.2])⟩

/-- The true walk frame contains all differences of sampled displacements in
its fourfold rectangle. -/
theorem frame_difference_differences {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {z : ℕ → L} {N : ℕ} {D C H : ℝ}
    (F : ActualWalkFrame b e z N D C H) :
    ∀ x ∈ latticeDifferences (walkVertices z N),
      ∀ y ∈ latticeDifferences (walkVertices z N),
      x-y ∈ latticeRectangle b e F.orientation (4*F.length) (4*F.width) := by
  intro x hx y hy
  have hx' := F.difference_rectangle x hx
  have hy' := F.difference_rectangle y hy
  have hh := latticeRectangle_sub b e F.orientation hx' hy'
  refine ⟨hh.1.trans ?_, ?_⟩
  · linarith [F.one_le_width, F.width_le_length]
  · convert hh.2 using 1; ring

lemma fresh_error_bounds {g L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hL : 1 ≤ L) (hr : 0 < r) (hlarge : 5120 ≤ g^4*r) :
    r*(Real.log 2)^2/(2*g*r*L)^2 ≤ g ∧ Real.exp (-(g^3*r/5120)) ≤ g := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hl2 : (Real.log 2)^2 ≤ 1 := by nlinarith
  have hg4 : 0 < g^4 := pow_pos hg _
  have hg3 : 0 < g^3 := pow_pos hg _
  have hgL : 0 < 2*g*r*L := by positivity
  have hgr : 1 ≤ g^3*r := by
    have h : g^4*r = g*(g^3*r) := by ring
    have hp : 0 ≤ g^3*r := mul_nonneg hg3.le hr.le
    nlinarith
  have hLL : 1 ≤ L^2 := by nlinarith
  have hprod := mul_le_mul hgr hLL (by norm_num : (0:ℝ)≤1) (mul_nonneg hg3.le hr.le)
  have hrr : 0 ≤ r*(4*(g^3*r*L^2)-1) := mul_nonneg hr.le (by nlinarith)
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hgL)).mpr
    have h := mul_le_mul_of_nonneg_left hl2 hr.le
    nlinarith
  · have hpow : 1/g ≤ g^3*r/5120 := by
      apply (div_le_iff₀ hg).mpr
      nlinarith
    have hlogg : -(1/g) ≤ Real.log g := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
      rw [Real.log_inv] at h
      simp only [one_div] at h ⊢
      linarith
    exact (Real.exp_le_exp.mpr (by linarith : -(g^3*r/5120) ≤ Real.log g)).trans_eq
      (Real.exp_log hg)

lemma fresh_gap_bound {g a L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (ha : 0 ≤ a) (hlow : (1+10*g)*a ≤ r*L) :
    a ≤ (1-g)*(r*L-2*g*r*L) := by
  have hfac : 0 ≤ (1-g)*(1-2*g) := mul_nonneg (by linarith) (by linarith)
  have h := mul_le_mul_of_nonneg_left hlow hfac
  have hn : 0 ≤ g*(7-30*g) := mul_nonneg hg.le (by linarith)
  have he : 1 ≤ (1-g)*(1-2*g)*(1+10*g) := by
    have hg3 : 0 ≤ g^3 := pow_nonneg hg.le _
    nlinarith
  have ha' := mul_le_mul_of_nonneg_right he ha
  nlinarith

theorem differenceLaw_fresh_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes)
    (z : ℕ → L) (n : ℕ) {m r : ℕ}
    (hbr : m < r) (hr : r ≤ S.card)
    {T R W g a : ℝ} (o : Plane ≃ₗᵢ[ℝ] Plane) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hmean : 1 ≤ FreshEntropy.batchMeanLog S) (ha : Real.log ((max (2 / |planarCellDet e|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤ a) (ha0 : 0 ≤ a)
    (hlow : (1+10*g)*a ≤ r*FreshEntropy.batchMeanLog S) (hhigh : r*FreshEntropy.batchMeanLog S ≤ (1+11*g)*a)
    (hlarge : 5120 ≤ g^4*r)
    (hsize : (1-g)*a ≤ Real.log (latticeDifferences (walkVertices z n)).card)
    (hcost : 2*m*Real.log (2*T) ≤ 8*g*a)
    (hΔ : ∀ x ∈ latticeDifferences (walkVertices z n), ∀ y ∈ latticeDifferences (walkVertices z n),
      x-y ∈ latticeRectangle b e o R W) :
    (1-30*g)*FreshEntropy.batchMeanLog S ≤ signedFreshCoordinate data S (walkDifferenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) m (by omega) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hg14 : g < 1/4 := by linarith
  have hδ : 0 < 2*g*r*FreshEntropy.batchMeanLog S := by positivity
  have hgap : Real.log ((max (2 / |planarCellDet e|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤ (1-g)*(r*FreshEntropy.batchMeanLog S-2*g*r*FreshEntropy.batchMeanLog S) := by
    exact ha.trans (fresh_gap_bound hg hg1 ha0 hlow)
  have hlarge' : 1000 ≤ g^3*(r:ℝ) := by
    have hp : 0 ≤ g^3*(r:ℝ) := by positivity
    have hid : g^4*(r:ℝ) = g*(g^3*r) := by ring
    nlinarith
  have herr := fresh_error_bounds hg hg1 hmean hr0 hlarge
  have h := differenceLaw_fresh data b e hArith S hS z n hbr hr o hT hpT hW hWR hg hg14 hδ
    hgap hlarge' hΔ
  have hsize0 : 0 ≤ Real.log (latticeDifferences (walkVertices z n)).card := by
    have hh : 0 ≤ (1-g)*a := mul_nonneg (by linarith) ha0
    linarith
  have he := mul_le_mul_of_nonneg_right (show 1-2*g ≤
      1-(r:ℝ)*(Real.log 2)^2/(2*g*r*FreshEntropy.batchMeanLog S)^2-
        Real.exp (-(g^3*r/5120)) by linarith [herr.1,herr.2]) hsize0
  have hs := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1-2*g by linarith)
  have hnum : (1-11*g)*a ≤ (r-m:ℕ)*signedFreshCoordinate data S (walkDifferenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) m (by omega) := by
    have hx : 0 ≤ 2*g^2*a := by positivity
    nlinarith
  have hp0 : 0 ≤ 1-30*g := by linarith
  have hh := mul_le_mul_of_nonneg_left hhigh hp0
  have hh2 : (1-30*g)*((1+11*g)*a) ≤ (1-11*g)*a := by
    have h1 : 0 ≤ g*a := mul_nonneg hg.le ha0
    have h2 : 0 ≤ g^2*a := mul_nonneg (sq_nonneg _) ha0
    nlinarith
  have hbrR : (r-m:ℕ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r m
  have hb0 : (0:ℝ) < (r-m:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbr
  have hm := mul_le_mul_of_nonneg_right hbrR (mul_nonneg hp0 (by linarith : 0 ≤ FreshEntropy.batchMeanLog S))
  nlinarith


/-- The true frame packing bound gives the required lower area scale. -/
theorem frame_log_packing {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    {z : ℕ → L} {N : ℕ} {D C H : ℝ} (F : ActualWalkFrame b e z N D C H)
    (hC : 0 < C) (hN : 1 ≤ N) :
    Real.log N - Real.log C ≤ Real.log (F.length * F.width) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 0 < F.length := by linarith [F.one_le_width,F.width_le_length]
  have hW : 0 < F.width := by linarith [F.one_le_width]
  have hle : (N : ℝ) ≤ C * (F.length * F.width) := by linarith [F.packing]
  have hh := Real.log_le_log hNp hle
  rw [Real.log_mul hC.ne' (mul_pos hR hW).ne'] at hh
  linarith only [hh]

/-- Genuine many-differences geometry supplies the displacement-size entropy
lower bound, with the actual step ball and true cell area retained. -/
theorem frame_log_difference_size {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {z : ℕ → L} {N : ℕ} {D C H : ℝ}
    (F : ActualWalkFrame b e z N D C H) (hH : 1 ≤ H) :
    Real.log (F.length * F.width) -
      Real.log (H * max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) ≤
        Real.log (latticeDifferences (walkVertices z N)).card := by
  have hR : 0 < F.length := by linarith [F.one_le_width,F.width_le_length]
  have hW : 0 < F.width := by linarith [F.one_le_width]
  have hHp : 0 < H := by linarith
  have hK : 0 < max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hΔp : (0 : ℝ) < (latticeDifferences (walkVertices z N)).card := by
    exact_mod_cast Finset.card_pos.mpr (walkDifferences_nonempty z N)
  have hbound : F.length * F.width ≤
      (H * max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) *
        (latticeDifferences (walkVertices z N)).card := F.area_differences
  have hh := Real.log_le_log (mul_pos hR hW) hbound
  rw [Real.log_mul (mul_pos hHp hK).ne' hΔp.ne'] at hh
  linarith only [hh]

noncomputable def rectanglePackingConstant (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : ℝ := (planarLatticeRectangle_packing b e).choose

/-- The walk displacement alphabet has an actual rectangle packing upper
bound. The constant is fixed by the actual lattice before choosing the walk. -/
theorem frame_log_difference_support {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {z : ℕ → L} {N : ℕ} {D C H : ℝ}
    (F : ActualWalkFrame b e z N D C H) :
    Real.log (latticeDifferences (walkVertices z N)).card ≤
      Real.log (4 * rectanglePackingConstant b e) + Real.log (F.length * F.width) := by
  have hp := (planarLatticeRectangle_packing b e).choose_spec
  have hCp : 0 < rectanglePackingConstant b e := hp.1
  have hRp : 0 < F.length := by linarith [F.one_le_width,F.width_le_length]
  have hWp : 0 < F.width := by linarith [F.one_le_width]
  let c0 : Plane := EuclideanSpace.single 0 (-F.length)
  let c := F.orientation.symm c0
  have he (x : L) : F.orientation (planarEmbedding b e x - c) =
      F.orientation (planarEmbedding b e x) - c0 := by
    rw [map_sub]
    simp only [c, LinearIsometryEquiv.apply_symm_apply]
  have hpack := hp.2 F.orientation c (latticeDifferences (walkVertices z N))
    (2*F.length) (2*F.width) (by linarith [F.one_le_width,F.width_le_length])
    (by linarith [F.one_le_width]) (by
      intro x hx
      have hh := F.difference_rectangle x hx
      have hr := abs_le.mp hh.1
      rw [he]
      simp [c0, PiLp.sub_apply]
      exact ⟨by linarith, by linarith, hh.2⟩)
  have hΔp : (0 : ℝ) < (latticeDifferences (walkVertices z N)).card := by
    exact_mod_cast Finset.card_pos.mpr (walkDifferences_nonempty z N)
  have hbound : ((latticeDifferences (walkVertices z N)).card : ℝ) ≤
      (4*rectanglePackingConstant b e)*(F.length*F.width) := by
    dsimp only [rectanglePackingConstant]
    nlinarith only [hpack]
  have hh := Real.log_le_log hΔp hbound
  rw [Real.log_mul (mul_pos (by norm_num) hCp).ne' (mul_pos hRp hWp).ne'] at hh
  exact hh

noncomputable def geometricScale (data : SignedResidueData L)
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (hArith : ArithmeticInterface data b e) : ℝ :=
  max 1 (max (2 / |planarCellDet e|)
    (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))

/-- The actual walk frame discharges the geometry and displacement-size
inputs of the paper's scalar fresh lower bound. All constants are genuine
lattice constants, and the conclusion uses the actual walk displacement law. -/
theorem frame_fresh_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (hne : S.Nonempty)
    (z : ℕ → L) {n : ℕ} (hn : 1 ≤ n) {D C H T g : ℝ}
    (F : ActualWalkFrame b e z n D C H) (hC : 0 < C) (hH : 1 ≤ H)
    (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ FreshEntropy.batchMeanLog S)
    {m : ℕ} (hu : 0 < Real.log n-Real.log C)
    (hround : FreshEntropy.batchMeanLog S ≤ g*(Real.log n-Real.log C))
    (hlarge : 5120*FreshEntropy.batchMeanLog S ≤ g^4*(Real.log n-Real.log C))
    (hcost : (m:ℝ)*FreshEntropy.batchMeanLog S ≤ g*(Real.log n-Real.log C))
    (hsize : Real.log (16*geometricScale data hArith) +
      Real.log (H * max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) ≤
      g*(Real.log n-Real.log C))
    (hcap : 2*(2*Real.log n+Real.log (16*geometricScale data hArith)+2*Real.log D) ≤
      S.card*FreshEntropy.batchMeanLog S) :
    ∃ hm : m < S.card,
      (1-30*g)*FreshEntropy.batchMeanLog S ≤
        signedFreshCoordinate data S (walkDifferenceLaw z n)
          (fun ij => z ij.1.val) (fun ij => z ij.2.val) m hm := by
  let R := F.length
  let W := F.width
  let A := geometricScale data hArith
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAp : 0 < A := by linarith only [hA1]
  have hRp : 0 < R := by dsimp [R]; linarith [F.one_le_width,F.width_le_length]
  have hWp : 0 < W := by dsimp [W]; linarith [F.one_le_width]
  have hRW : 0 < R*W := mul_pos hRp hWp
  have h16 : 0 < 16*A := by positivity
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hLp : 0 < FreshEntropy.batchMeanLog S := by linarith only [hL]
  let a := Real.log (16*A*(R*W))
  let u := Real.log n-Real.log C
  have haeq : a = Real.log (16*A)+Real.log (R*W) := Real.log_mul h16.ne' hRW.ne'
  have hua : u ≤ a := by
    have hh := frame_log_packing F hC hn
    have hln : 0 ≤ Real.log (16*A) := Real.log_nonneg (by nlinarith only [hA1])
    change u ≤ Real.log (R*W) at hh
    linarith only [hh,haeq,hln]
  have ha0 : 0 < a := lt_of_lt_of_le hu hua
  have hav : a ≤ 2*Real.log n+Real.log (16*A)+2*Real.log D := by
    have hh := Real.log_le_log hRW (F.area_upper_of_one_le hn hD)
    rw [Real.log_mul (pow_ne_zero _ (by linarith : D≠0)) (pow_ne_zero _ hnR.ne'),
      Real.log_pow,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,haeq]
  let r := ⌈(1+10*g)*a/FreshEntropy.batchMeanLog S⌉₊
  have hlo : (1+10*g)*a ≤ (r:ℝ)*FreshEntropy.batchMeanLog S := by
    exact (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi : (r:ℝ)*FreshEntropy.batchMeanLog S ≤ (1+11*g)*a := by
    have hx : 0 ≤ (1+10*g)*a/FreshEntropy.batchMeanLog S := by positivity
    have hc := Nat.ceil_lt_add_one hx
    have hh := mul_lt_mul_of_pos_right hc hLp
    have heq : ((1+10*g)*a/FreshEntropy.batchMeanLog S+1)*FreshEntropy.batchMeanLog S =
        (1+10*g)*a+FreshEntropy.batchMeanLog S := by
      rw [add_mul,div_mul_cancel₀ _ hLp.ne',one_mul]
    rw [heq] at hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    change (r:ℝ)*FreshEntropy.batchMeanLog S < (1+10*g)*a+FreshEntropy.batchMeanLog S at hh
    nlinarith only [hh,hround,hgu]
  have hr : r ≤ S.card := by
    suffices hh : (r:ℝ) ≤ S.card by exact_mod_cast hh
    have hh : (1+11*g)*a ≤ 2*a := by nlinarith only [hg1,ha0]
    nlinarith only [hhi,hh,hav,hcap,hLp]
  have hmr : m < r := by
    suffices hh : (m:ℝ) < r by exact_mod_cast hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    nlinarith only [hcost,hgu,hlo,hg1,hLp,ha0]
  have hlr : 5120 ≤ g^4*(r:ℝ) := by
    have hg4 : 0 < g^4 := pow_pos hg _
    have h1 : u ≤ (r:ℝ)*FreshEntropy.batchMeanLog S := by nlinarith only [hlo,hua,hg,ha0]
    have h2 := mul_le_mul_of_nonneg_left h1 hg4.le
    nlinarith only [h2,hlarge,hLp]
  have hsz : (1-g)*a ≤ Real.log (latticeDifferences (walkVertices z n)).card := by
    have hh := frame_log_difference_size F hH
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    change Real.log (R*W)-_ ≤ _ at hh
    nlinarith only [hh,hgu,haeq,hsize]
  have hlog2 : Real.log (2*T) ≤ 2*FreshEntropy.batchMeanLog S := by
    let _ : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hne)
    have hm : Real.log T ≤ FreshEntropy.batchMeanLog S := by
      have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
        Real.log_le_log (by linarith : 0 < T) (hpT _ (signedBatchPrime_mem S i)).1)
      simpa only [FreshEntropy.batchMeanLog,Fintype.expect_const] using hh
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : T≠0)]
    linarith only [hm,hlog2,hL]
  have hmc : 2*(m:ℝ)*Real.log (2*T) ≤ 8*g*a := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ)≤2*m)
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    have hga : 0 ≤ g*a := by positivity
    nlinarith only [hh,hgu,hcost,hga]
  refine ⟨by omega, ?_⟩
  apply differenceLaw_fresh_lower data b e hArith S hS z n hmr hr F.orientation
    (R := 4*R) (W := 4*W) hT hpT
    (by dsimp [W]; linarith [F.one_le_width])
    (by dsimp [R,W]; linarith [F.width_le_length]) hg hg1 hL
    (a := a) ?_ ha0.le hlo hhi hlr hsz hmc
  · exact frame_difference_differences F
  · have hs : max (2 / |planarCellDet e|)
        (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) ≤ A := le_max_right _ _
    apply Real.log_le_log (by
      have hpos : 0 < max (2 / |planarCellDet e|)
          (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) :=
        (div_pos (by norm_num) (abs_pos.mpr (planarCellDet_ne_zero e))).trans_le (le_max_left _ _)
      positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hs hRW.le]


/-- Fixed lattice constants from the proved all-walk frame theorem. -/
noncomputable def walkPackingConstant (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : ℝ := (actual_walk_frame_package b e).choose

noncomputable def walkFrameFactor (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : ℝ :=
  (actual_walk_frame_package b e).choose_spec.choose

theorem walkFrameConstants_spec (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    0 < walkPackingConstant b e ∧ 1 ≤ walkFrameFactor b e ∧
      ∀ (z : ℕ → L) (N : ℕ) (D : ℝ), 1 ≤ N → 0 ≤ D →
      (∀ i ≤ N, ∀ j ≤ N, z i = z j → i = j) →
      (∀ t < N, dist (planarEmbedding b e (z t))
        (planarEmbedding b e (z (t+1))) ≤ D) →
      Nonempty (ActualWalkFrame b e z N D (walkPackingConstant b e) (walkFrameFactor b e)) :=
  (actual_walk_frame_package b e).choose_spec.choose_spec

/-- All-walk actual fresh entropy: the frame, packing, many differences, and
signed rectangle probability are proved dependencies. The remaining hypotheses
are exactly explicit scalar scale/capacity requirements for the prime batch. -/
theorem walk_fresh_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticInterface data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (hne : S.Nonempty)
    (z : ℕ → L) {n : ℕ} (hn : 1 ≤ n)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, z i = z j → i = j)
    {D T g : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hz : ∀ i < n, dist (planarEmbedding b e (z i))
      (planarEmbedding b e (z (i+1))) ≤ D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ FreshEntropy.batchMeanLog S)
    {m : ℕ} (hu : 0 < Real.log n-Real.log (walkPackingConstant b e))
    (hround : FreshEntropy.batchMeanLog S ≤ g*(Real.log n-Real.log (walkPackingConstant b e)))
    (hlarge : 5120*FreshEntropy.batchMeanLog S ≤
      g^4*(Real.log n-Real.log (walkPackingConstant b e)))
    (hcost : (m:ℝ)*FreshEntropy.batchMeanLog S ≤
      g*(Real.log n-Real.log (walkPackingConstant b e)))
    (hsize : Real.log (16*geometricScale data hArith) +
      Real.log (walkFrameFactor b e *
        max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) ≤
      g*(Real.log n-Real.log (walkPackingConstant b e)))
    (hcap : 2*(2*Real.log n+Real.log (16*geometricScale data hArith)+2*Real.log D) ≤
      S.card*FreshEntropy.batchMeanLog S) :
    ∃ hm : m < S.card,
      (1-30*g)*FreshEntropy.batchMeanLog S ≤
        signedFreshCoordinate data S (walkDifferenceLaw z n)
          (fun ij => z ij.1.val) (fun ij => z ij.2.val) m hm := by
  have hc := walkFrameConstants_spec b e
  obtain ⟨F⟩ := hc.2.2 z n D hn (by linarith only [hD]) hinj hz
  exact frame_fresh_lower data b e hArith S hS hne z hn F hc.1 hc.2.1 hD hT hpT
    hg hg1 hL hu hround hlarge hcost hsize hcap

end Entry002.WalkFreshEntropy
