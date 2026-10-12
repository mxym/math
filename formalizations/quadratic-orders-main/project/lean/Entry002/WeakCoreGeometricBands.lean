import Entry002.GenericGeometricScale
import Entry002.GenericBandParameters
import Entry002.ArithmeticCore
import Entry002.GenericGeometricBands
import Entry002.WeakCoreGeometricScale

/-! Core-only replay of the round-five owned `GenericGeometricBands` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Uniform actual geometric band enrichment. The scalar margins for every
stage are constructed from the floor-based band parameters and the proved
lattice threshold; no geometric or fresh-information certificate is assumed. -/
set_option autoImplicit false
namespace Entry002.WeakA5
open Module Filter
open OAI.GaussianMoat
open _root_.Entry002.WeakA5.WalkFreshEntropy
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- A single lattice threshold works for all actual prime batches, all walks,
and all finite band schedules whose displayed relative size/capacity conditions
hold at each stage. The resulting law is the genuine composed endpoint law. -/
theorem uniform_band_geometric_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ (S : Finset ℕ) (X : ℝ),
      (∀ p ∈ S, p ∈ data.primes) → S.Nonempty →
      1 ≤ _root_.Entry002.FreshEntropy.batchMeanLog S → _root_.Entry002.FreshEntropy.batchMeanLog S ≤ 2*X →
      ∀ (P : TimeLaw) (z : ℕ → L), Function.Injective z →
      (∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D) →
      ∀ T : ℝ, 5 ≤ T → (∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) →
      ∀ U : ℝ, ∀ l : ℕ,
      (∀ j<l, U₀ ≤ bandScale g U j) →
      (∀ j<l, 1280*X ≤ g^5*bandScale g U j) →
      (∀ j<l, bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j ≤ S.card) →
      let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
      (1-(1/2:ℝ)^l-80*g)*(bandSize μ g U l:ℝ)*μ ≤
        signedPointEntropy data S (P.run z (bandLength g U) l).law
          (fun a => z a.val) (bandSize μ g U l) := by
  obtain ⟨u₀, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_uniform_geometric_fresh_scales data b e hArith hD hg hg1)
  refine ⟨max 1 u₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro S X hS hne hmean hmeanup P z hinj hs T hT hpT U l hscale hrelative hcap
  let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
  have hmarg (j : ℕ) (hj : j<l) :
      0<bandSize μ g U (j+1) ∧ bandSize μ g U (j+1)<bandSize μ g U j ∧
      bandSize μ g U j≤S.card ∧ (bandSize μ g U (j+1):ℝ)≤(2*g)*bandSize μ g U j ∧
      GeometricFreshScale data b e hArith S D (2*g) (bandLength g U j)
        (bandSize μ g U (j+1)) ∧
      2*Real.log (wordStepBall b e (D*bandLength g U j)).card≤
        8*(2*g)*bandSize μ g U j*μ := by
    have hh := hthreshold (bandScale g U j) ((le_max_right _ _).trans (hscale j hj))
      S X hmean hmeanup (hrelative j hj) (hcap j hj)
    simpa only [bandLength,bandSize,bandScale_succ] using hh
  have h := Entry002.WeakA5.TimeLaw.iterated_geometric_entropy P data S hS hne b e hArith z hinj hD hT hs hpT
    (mul_pos (by norm_num) hg) (by linarith only [hg1]) hmean
    (bandLength g U) (bandSize μ g U) l
    (fun j hj => ⟨(hmarg j hj).1,(hmarg j hj).2.1,
      (hmarg j hj).2.2.1,(hmarg j hj).2.2.2.1⟩)
    (fun j hj => (hmarg j hj).2.2.2.2.1)
    (fun j hj => (hmarg j hj).2.2.2.2.2)
  convert h using 1; ring

/-- The same uniform band estimate for the literal endpoint schedule followed
by its true uniform smoothing kernel, with actual derived suffix-ball cost. -/
theorem uniform_band_common_geometric_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ (S : Finset ℕ) (X : ℝ),
      (∀ p ∈ S, p ∈ data.primes) → S.Nonempty →
      1 ≤ _root_.Entry002.FreshEntropy.batchMeanLog S → _root_.Entry002.FreshEntropy.batchMeanLog S ≤ 2*X →
      ∀ (P : TimeLaw) (z : ℕ → L), Function.Injective z →
      (∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D) →
      ∀ T : ℝ, 5 ≤ T → (∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) →
      ∀ U : ℝ, ∀ l : ℕ,
      (∀ j<l, U₀ ≤ bandScale g U j) →
      (∀ j<l, 1280*X ≤ g^5*bandScale g U j) →
      (∀ j<l, bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j ≤ S.card) →
      ∀ (N : ℕ) (err : ℝ),
      Real.log (wordStepBall b e (D*N)).card≤
        err*(bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S →
      let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
      (1-(1/2:ℝ)^l-80*g-err)*(bandSize μ g U l:ℝ)*μ ≤
        signedPointEntropy data S (P.advance (commonSchedule z
          (List.ofFn (fun i : Fin l => bandLength g U i.val)) N)).law
          (fun a => z a.val) (bandSize μ g U l) := by
  obtain ⟨U₀,hU₀,hband⟩ := uniform_band_geometric_entropy data b e hArith hD hg hg1
  refine ⟨U₀,hU₀,?_⟩
  intro S X hS hne hmean hmeanup P z hinj hs T hT hpT U l hscale hrelative hcap N err hsuffix
  have hbase := hband S X hS hne hmean hmeanup P z hinj hs T hT hpT U l hscale hrelative hcap
  dsimp only at hbase
  have hloss := (P.run z (bandLength g U) l).advance_entropy (smoothingKernel N)
    data S hS b e z (by linarith only [hD]) hs (bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l)
  rw [P.run_common]
  have hbound : (smoothingKernel N).bound = N := rfl
  rw [hbound] at hloss
  nlinarith only [hbase,hloss,hsuffix]

/-- Explicit polynomial threshold version of the genuine band estimate.
The lattice constant is independent of `g`, so this applies to varying accurate
grids as soon as `C ≤ g² Uⱼ` holds at every stage. -/
theorem explicit_band_geometric_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200)
    (S : Finset ℕ) (X : ℝ) (hS : ∀ p ∈ S, p ∈ data.primes) (hne : S.Nonempty)
    (hmean : 1 ≤ _root_.Entry002.FreshEntropy.batchMeanLog S)
    (hmeanup : _root_.Entry002.FreshEntropy.batchMeanLog S ≤ 2*X)
    (P : TimeLaw) (z : ℕ → L) (hinj : Function.Injective z)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D)
    (T : ℝ) (hT : 5 ≤ T) (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (U : ℝ) (l : ℕ)
    (hguard : ∀ j<l, geometricGuardConstant data b e hArith D ≤ g^2*bandScale g U j)
    (hrelative : ∀ j<l, 1280*X ≤ g^5*bandScale g U j)
    (hcap : ∀ j<l, bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j ≤ S.card) :
    let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
    (1-(1/2:ℝ)^l-80*g)*(bandSize μ g U l:ℝ)*μ ≤
      signedPointEntropy data S (P.run z (bandLength g U) l).law
        (fun a => z a.val) (bandSize μ g U l) := by
  let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
  have hmarg (j : ℕ) (hj : j<l) :
      0<bandSize μ g U (j+1) ∧ bandSize μ g U (j+1)<bandSize μ g U j ∧
      bandSize μ g U j≤S.card ∧ (bandSize μ g U (j+1):ℝ)≤(2*g)*bandSize μ g U j ∧
      GeometricFreshScale data b e hArith S D (2*g) (bandLength g U j)
        (bandSize μ g U (j+1)) ∧
      2*Real.log (wordStepBall b e (D*bandLength g U j)).card≤
        8*(2*g)*bandSize μ g U j*μ := by
    have hh := uniform_geometric_fresh_scales_of_guard data b e hArith S
      hD hg hg1 (hguard j hj) hmean hmeanup (hrelative j hj) (hcap j hj)
    simpa only [bandLength,bandSize,bandScale_succ] using hh
  have h := Entry002.WeakA5.TimeLaw.iterated_geometric_entropy P data S hS hne b e hArith z hinj hD hT hs hpT
    (mul_pos (by norm_num) hg) (by linarith only [hg1]) hmean
    (bandLength g U) (bandSize μ g U) l
    (fun j hj => ⟨(hmarg j hj).1,(hmarg j hj).2.1,
      (hmarg j hj).2.2.1,(hmarg j hj).2.2.2.1⟩)
    (fun j hj => (hmarg j hj).2.2.2.2.1)
    (fun j hj => (hmarg j hj).2.2.2.2.2)
  convert h using 1; ring

/-- Explicit varying-grid estimate for the common endpoint schedule with its
actual smoothing kernel and actual displacement-ball cost. -/
theorem explicit_band_common_geometric_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200)
    (S : Finset ℕ) (X : ℝ) (hS : ∀ p ∈ S, p ∈ data.primes) (hne : S.Nonempty)
    (hmean : 1 ≤ _root_.Entry002.FreshEntropy.batchMeanLog S)
    (hmeanup : _root_.Entry002.FreshEntropy.batchMeanLog S ≤ 2*X)
    (P : TimeLaw) (z : ℕ → L) (hinj : Function.Injective z)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D)
    (T : ℝ) (hT : 5 ≤ T) (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (U : ℝ) (l : ℕ)
    (hguard : ∀ j<l, geometricGuardConstant data b e hArith D ≤ g^2*bandScale g U j)
    (hrelative : ∀ j<l, 1280*X ≤ g^5*bandScale g U j)
    (hcap : ∀ j<l, bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j ≤ S.card)
    (N : ℕ) (err : ℝ)
    (hsuffix : Real.log (wordStepBall b e (D*N)).card≤
      err*(bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
    (1-(1/2:ℝ)^l-80*g-err)*(bandSize μ g U l:ℝ)*μ ≤
      signedPointEntropy data S (P.advance (commonSchedule z
        (List.ofFn (fun i : Fin l => bandLength g U i.val)) N)).law
        (fun a => z a.val) (bandSize μ g U l) := by
  have hbase := explicit_band_geometric_entropy data b e hArith hD hg hg1
    S X hS hne hmean hmeanup P z hinj hs T hT hpT U l hguard hrelative hcap
  dsimp only at hbase
  have hloss := (P.run z (bandLength g U) l).advance_entropy (smoothingKernel N)
    data S hS b e z (by linarith only [hD]) hs (bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l)
  rw [P.run_common]
  have hbound : (smoothingKernel N).bound = N := rfl
  rw [hbound] at hloss
  nlinarith only [hbase,hloss,hsuffix]

end Entry002.WeakA5
