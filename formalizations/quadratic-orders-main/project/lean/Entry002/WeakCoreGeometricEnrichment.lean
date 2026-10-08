import Entry002.GenericWalkFreshEntropy
import Entry002.GenericMultiscaleEnrichment
import Entry002.ArithmeticCore
import Entry002.GenericGeometricEnrichment
import Entry002.WeakCoreWalkFreshEntropy

/-! Core-only replay of the round-five owned `GenericGeometricEnrichment` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Actual geometric endpoint enrichment. The fresh inputs to the genuine
TimeLaw step and iteration are derived at every natural starting position from
walk geometry, A2/A4 signed separation, and actual displacement entropy. -/
set_option autoImplicit false
namespace Entry002.WeakA5
open Module
open OAI.GaussianMoat
open _root_.Entry002.WeakA5.WalkFreshEntropy
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- Explicit scalar scale conditions; every field is an elementary numerical
inequality. No fresh-entropy or geometric result is stored in this structure. -/
structure GeometricFreshScale (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ) (D g : ℝ) (n m : ℕ) : Prop where
  length_pos : 1 ≤ n
  positive_log : 0 < Real.log n-Real.log (walkPackingConstant b e)
  rounding : _root_.Entry002.FreshEntropy.batchMeanLog S ≤ g*(Real.log n-Real.log (walkPackingConstant b e))
  large : 5120*_root_.Entry002.FreshEntropy.batchMeanLog S ≤ g^4*(Real.log n-Real.log (walkPackingConstant b e))
  index_cost : (m:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S ≤ g*(Real.log n-Real.log (walkPackingConstant b e))
  size : Real.log (16*geometricScale data hArith) +
    Real.log (walkFrameFactor b e *
      max 1 (max D ((planarLatticeBall b e (4*D)).card * |planarCellDet e|))) ≤
    g*(Real.log n-Real.log (walkPackingConstant b e))
  capacity : 2*(2*Real.log n+Real.log (16*geometricScale data hArith)+2*Real.log D) ≤
    S.card*_root_.Entry002.FreshEntropy.batchMeanLog S

/-- The actual geometric fresh lower bound holds at every natural starting
position of the same self-avoiding bounded-step walk. -/
theorem shifted_walk_fresh_lower (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (hne : S.Nonempty)
    (z : ℕ → L) (hinj : Function.Injective z) {D T g : ℝ}
    (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hmean : 1 ≤ _root_.Entry002.FreshEntropy.batchMeanLog S)
    {n m : ℕ} (hscale : GeometricFreshScale data b e hArith S D g n m)
    (a : ℕ) :
    ∃ hm : m < S.card,
      (1-30*g)*_root_.Entry002.FreshEntropy.batchMeanLog S ≤ signedFreshCoordinate data S
        (walkDifferenceLaw (fun t => z (a+t)) n)
        (fun ij => z (a+ij.1.val)) (fun ij => z (a+ij.2.val)) m hm := by
  apply walk_fresh_lower data b e hArith S hS hne (fun t => z (a+t)) hscale.length_pos
    (fun i _ j _ h => Nat.add_left_cancel (hinj h)) hD hT
    (fun i _ => by simpa only [Nat.add_assoc] using hs (a+i)) hpT hg hg1 hmean
    hscale.positive_log hscale.rounding hscale.large hscale.index_cost hscale.size hscale.capacity

/-- A genuine geometric step deficit, with its fresh input proved uniformly
at all starts from the actual walk and displayed scalar conditions. -/
theorem TimeLaw.geometric_step_deficit (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (hne : S.Nonempty) (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (z : ℕ → L) (hinj : Function.Injective z)
    {D T g deficit : ℝ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0<g) (hg1 : g≤1/100) (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    {n s q : ℕ} (hspos : 0<s) (hsq : s<q) (hq : q≤S.card)
    (hratio : (s:ℝ)≤g*q)
    (hscale : GeometricFreshScale data b e hArith S D g n s)
    (hE : (1-deficit)*(q:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S≤
      signedPointEntropy data S P.law (fun a => z a.val) q)
    (hcost : 2*Real.log (wordStepBall b e (D*n)).card≤8*g*q*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    (1-deficit/2-20*g)*(s:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S≤
      signedPointEntropy data S (P.step z n).law (fun a => z a.val) s := by
  apply P.step_deficit data S hS b e z (by linarith only [hD]) hs hspos hsq hq
    hg.le hg1 (by linarith only [hmean]) hratio ?_ hE hcost
  intro a
  obtain ⟨hm, hf⟩ := shifted_walk_fresh_lower data b e hArith S hS hne z hinj
    hD hT hs hpT hg hg1 hmean hscale a
  exact hf

/-- Iterated entropy for the genuine composed endpoint law. Every stage's
fresh information is proved geometrically; only explicit scalar stage scales,
index ratios, and actual finite-ball displacement costs remain hypotheses. -/
theorem TimeLaw.iterated_geometric_entropy (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (hne : S.Nonempty) (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (z : ℕ → L) (hinj : Function.Injective z)
    {D T g : ℝ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0<g) (hg1 : g≤1/100) (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    (length q : ℕ → ℕ) (l : ℕ)
    (hm : ∀j<l, 0<q (j+1) ∧ q (j+1)<q j ∧ q j≤S.card ∧ (q (j+1):ℝ)≤g*q j)
    (hscale : ∀j<l, GeometricFreshScale data b e hArith S D g (length j) (q (j+1)))
    (hcost : ∀j<l, 2*Real.log (wordStepBall b e (D*length j)).card≤
      8*g*q j*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    (1-(1/2:ℝ)^l-40*g)*(q l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S≤
      signedPointEntropy data S (P.run z length l).law (fun a => z a.val) (q l) := by
  apply P.run_entropy data S hS b e z (by linarith only [hD]) hs hg.le hg1
    (by linarith only [hmean]) length q l hm ?_ hcost
  intro j hj a
  obtain ⟨hi, hf⟩ := shifted_walk_fresh_lower data b e hArith S hS hne z hinj
    hD hT hs hpT hg hg1 hmean (hscale j hj) a
  exact hf

/-- Actual later kernels lose only their derived finite-ball displacement
entropy; all earlier fresh inputs remain proved geometric conclusions. -/
theorem TimeLaw.future_geometric_entropy (P : TimeLaw) (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (hne : S.Nonempty) (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (z : ℕ → L) (hinj : Function.Injective z)
    {D T g err : ℝ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0<g) (hg1 : g≤1/100) (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    (length q : ℕ → ℕ) (l : ℕ)
    (hm : ∀j<l, 0<q (j+1) ∧ q (j+1)<q j ∧ q j≤S.card ∧ (q (j+1):ℝ)≤g*q j)
    (hscale : ∀j<l, GeometricFreshScale data b e hArith S D g (length j) (q (j+1)))
    (hcost : ∀j<l, 2*Real.log (wordStepBall b e (D*length j)).card≤
      8*g*q j*_root_.Entry002.FreshEntropy.batchMeanLog S)
    (hsuffix : Real.log (wordStepBall b e (D*K.bound)).card≤
      err*(q l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    (1-(1/2:ℝ)^l-40*g-err)*(q l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S≤
      signedPointEntropy data S ((P.run z length l).advance K).law (fun a => z a.val) (q l) := by
  apply P.run_future_entropy K data S hS b e z (by linarith only [hD]) hs hg.le hg1
    (by linarith only [hmean]) length q l hm ?_ hcost hsuffix
  intro j hj a
  obtain ⟨hi, hf⟩ := shifted_walk_fresh_lower data b e hArith S hS hne z hinj
    hD hT hs hpT hg hg1 hmean (hscale j hj) a
  exact hf

/-- Entropy of the literal common endpoint schedule followed by its true
uniform smoothing kernel. No separate fresh-information premise is used. -/
theorem TimeLaw.common_geometric_entropy (P : TimeLaw) (N : ℕ)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (hne : S.Nonempty) (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (z : ℕ → L) (hinj : Function.Injective z)
    {D T g err : ℝ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hpT : ∀ p ∈ S, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0<g) (hg1 : g≤1/100) (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    (length q : ℕ → ℕ) (l : ℕ)
    (hm : ∀j<l, 0<q (j+1) ∧ q (j+1)<q j ∧ q j≤S.card ∧ (q (j+1):ℝ)≤g*q j)
    (hscale : ∀j<l, GeometricFreshScale data b e hArith S D g (length j) (q (j+1)))
    (hcost : ∀j<l, 2*Real.log (wordStepBall b e (D*length j)).card≤
      8*g*q j*_root_.Entry002.FreshEntropy.batchMeanLog S)
    (hsuffix : Real.log (wordStepBall b e (D*N)).card≤
      err*(q l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    (1-(1/2:ℝ)^l-40*g-err)*(q l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S≤
      signedPointEntropy data S (P.advance (commonSchedule z (List.ofFn (fun i : Fin l => length i.val)) N)).law (fun a => z a.val) (q l) := by
  rw [P.run_common]
  exact Entry002.WeakA5.TimeLaw.future_geometric_entropy P (smoothingKernel N) data S hS hne b e hArith z hinj
    hD hT hs hpT hg hg1 hmean length q l hm hscale hcost hsuffix

end Entry002.WeakA5
