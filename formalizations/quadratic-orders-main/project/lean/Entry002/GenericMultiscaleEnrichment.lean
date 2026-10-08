import Entry002.GenericStepEnrichment
import Entry002.GenericWalkPackage

/-! Iterated actual endpoint enrichment. The fresh-coordinate lower bounds
and displayed finite-ball costs remain explicit mathematical obligations;
no geometric enrichment certificate is presumed true. Generic scalar deficit
accounting is replayed verbatim from pinned Information.lean lines115--139.
The actual iteration uses the proved fair-endpoint step theorem. -/
set_option autoImplicit false
namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

lemma entropy_step_deficit {b q : ℕ} {L F E E' g e C : ℝ}
    (hq : 0 < q) (hL : 0 ≤ L) (hg : 0 ≤ g) (hg1 : g ≤ 1/100)
    (hbq : (b:ℝ) ≤ g*q) (hF : (1-30*g)*L ≤ F)
    (hE : (1-e)*(q:ℝ)*L ≤ E) (hC : C ≤ 8*g*q*L)
    (hstep : (b:ℝ)*((q-b:ℕ)*F+E-C) ≤ 2*(q:ℝ)*E') :
    (1-e/2-20*g)*(b:ℝ)*L ≤ E' := by
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hbqr : (b:ℝ) ≤ q := by nlinarith only [hbq,hg1,hqr]
  have hbqnat : b ≤ q := by exact_mod_cast hbqr
  rw [Nat.cast_sub hbqnat] at hstep
  have hqbn : 0 ≤ (q:ℝ)-b := by linarith only [hbqr]
  have hFb := mul_le_mul_of_nonneg_left hF hqbn
  have hgl : 0 ≤ (1-30*g)*L := mul_nonneg (by linarith only [hg1]) hL
  have hbL := mul_le_mul_of_nonneg_right hbq hgl
  have hgg := mul_nonneg (mul_nonneg hg hg) (mul_nonneg hqr.le hL)
  have hgql : 0 ≤ g*(q:ℝ)*L := by positivity
  have hcore : (2-e-40*g)*(q:ℝ)*L ≤ ((q:ℝ)-b)*F+E-C := by
    nlinarith only [hFb,hbL,hE,hC,hgg,hgql]
  have hm := mul_le_mul_of_nonneg_left hcore (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ)<2) hqr)).mp
  calc
    _ = (b:ℝ)*((2-e-40*g)*(q:ℝ)*L) := by ring
    _ ≤ (b:ℝ)*(((q:ℝ)-b)*F+E-C) := hm
    _ ≤ _ := hstep

theorem TimeLaw.step_deficit (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D g deficit μ : ℝ} (hD : 0≤D)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    {n s r : ℕ} (hspos : 0<s) (hsr : s<r) (hr : r≤S.card)
    (hg : 0≤g) (hg1 : g≤1/100) (hμ : 0≤μ) (hratio : (s:ℝ)≤g*r)
    (hfresh : ∀a : ℕ, (1-30*g)*μ≤signedFreshCoordinate data S
      (walkDifferenceLaw (fun t => z (a+t)) n)
      (fun ij => z (a+ij.1.val)) (fun ij => z (a+ij.2.val)) s (by omega))
    (hE : (1-deficit)*(r:ℝ)*μ≤signedPointEntropy data S P.law (fun a => z a.val) r)
    (hcost : 2*Real.log (wordStepBall b e (D*n)).card≤8*g*r*μ) :
    (1-deficit/2-20*g)*(s:ℝ)*μ≤
      signedPointEntropy data S (P.step z n).law (fun a => z a.val) s := by
  exact entropy_step_deficit (by omega) hμ hg hg1 hratio le_rfl hE hcost
    (P.step_enrichment data S hS b e z hD hs hspos hsr hr (fun a => hfresh a.val))

noncomputable def TimeLaw.run (P : TimeLaw) (z : ℕ → L) (length : ℕ → ℕ) : ℕ → TimeLaw
  | 0 => P
  | j+1 => (P.run z length j).step z (length j)

@[simp] lemma TimeLaw.run_zero (P : TimeLaw) (z : ℕ → L) (length : ℕ → ℕ) :
    P.run z length 0=P := rfl
@[simp] lemma TimeLaw.run_succ (P : TimeLaw) (z : ℕ → L) (length : ℕ → ℕ) (j : ℕ) :
    P.run z length (j+1)=(P.run z length j).step z (length j) := rfl

lemma signedPointEntropy_nonneg {Ω : Type*} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω) (Z : Ω → L) (s : ℕ) :
    0≤signedPointEntropy data S p Z s := by
  unfold signedPointEntropy FinLaw.signedEntropy
  exact Finset.expect_nonneg (fun _ _ => p.orderedEntropy_nonneg _ _)

/-- True iterated enrichment of the one actual endpoint-kernel walk law. The
uniform fresh-residue bounds and scalar costs are explicit inputs, to be
supplied by the separate geometric/parameter synthesis. -/
theorem TimeLaw.run_entropy (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D g μ : ℝ} (hD : 0≤D)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hg : 0≤g) (hg1 : g≤1/100) (hμ : 0≤μ)
    (length q : ℕ → ℕ) (l : ℕ)
    (hm : ∀j<l, 0<q (j+1) ∧ q (j+1)<q j ∧ q j≤S.card ∧ (q (j+1):ℝ)≤g*q j)
    (hfresh : ∀(j : ℕ) (hj : j<l) (a : ℕ), (1-30*g)*μ≤signedFreshCoordinate data S
      (walkDifferenceLaw (fun t => z (a+t)) (length j))
      (fun ij => z (a+ij.1.val)) (fun ij => z (a+ij.2.val)) (q (j+1))
      (by have := hm j hj; omega))
    (hcost : ∀j<l, 2*Real.log (wordStepBall b e (D*length j)).card≤8*g*q j*μ) :
    (1-(1/2:ℝ)^l-40*g)*(q l:ℝ)*μ≤
      signedPointEntropy data S (P.run z length l).law (fun a => z a.val) (q l) := by
  induction l with
  | zero =>
    have hn := signedPointEntropy_nonneg data S P.law (fun a => z a.val) (q 0)
    simp only [pow_zero,sub_self,zero_sub,TimeLaw.run_zero]
    have hneg : -(40*g)*(q 0:ℝ)*μ≤0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hg]) (Nat.cast_nonneg _)
      · exact hμ
    exact hneg.trans hn
  | succ l ih =>
    have hi := ih (fun j hj => hm j (by omega))
      (fun j hj a => hfresh j (by omega) a) (fun j hj => hcost j (by omega))
    have hh := (P.run z length l).step_deficit data S hS b e z hD hs
      (hm l (by omega)).1 (hm l (by omega)).2.1 (hm l (by omega)).2.2.1
      hg hg1 hμ (hm l (by omega)).2.2.2 (hfresh l (by omega))
      (deficit := (1/2:ℝ)^l+40*g) (by convert hi using 1; ring) (hcost l (by omega))
    rw [TimeLaw.run_succ]
    convert hh using 1; ring

lemma TimeLaw.advance_common_cons (P : TimeLaw) (z : ℕ → L)
    (n : ℕ) (ns : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (n::ns) N)=(P.step z n).advance (commonSchedule z ns N) := by
  rw [commonSchedule_cons,TimeLaw.advance_then,TimeLaw.advance_difference]

lemma TimeLaw.advance_common_append (P : TimeLaw) (z : ℕ → L)
    (ns ms : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (ns++ms) N)=
      (ns.foldl (fun Q k => Q.step z k) P).advance (commonSchedule z ms N) := by
  induction ns generalizing P with
  | nil => rfl
  | cons k ks hk =>
    rw [List.cons_append,TimeLaw.advance_common_cons,hk,List.foldl_cons]

lemma TimeLaw.foldl_ofFn (P : TimeLaw) (z : ℕ → L)
    (n : ℕ → ℕ) (l : ℕ) :
    (List.ofFn (fun i : Fin l => n i.val)).foldl (fun Q k => Q.step z k) P=P.run z n l := by
  induction l with
  | zero => rfl
  | succ l hl =>
    rw [List.ofFn_succ_last,List.foldl_append,List.foldl_cons,List.foldl_nil]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [hl,TimeLaw.run_succ]

lemma TimeLaw.run_common (P : TimeLaw) (z : ℕ → L)
    (n : ℕ → ℕ) (l N : ℕ) :
    P.advance (commonSchedule z (List.ofFn (fun i : Fin l => n i.val)) N)=
      (P.run z n l).advance (smoothingKernel N) := by
  have h := P.advance_common_append z (List.ofFn (fun i : Fin l => n i.val)) [] N
  simpa only [List.append_nil,TimeLaw.foldl_ofFn,commonSchedule,List.foldr_nil] using h


/-- Later actual forward kernels lose at most their derived finite-ball
displacement entropy. The numerical suffix-cost bound is displayed explicitly. -/
theorem TimeLaw.run_future_entropy (P : TimeLaw) (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀p∈S, p∈data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D g μ err : ℝ} (hD : 0≤D)
    (hs : ∀t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (hg : 0≤g) (hg1 : g≤1/100) (hμ : 0≤μ)
    (length q : ℕ → ℕ) (l : ℕ)
    (hm : ∀j<l, 0<q (j+1) ∧ q (j+1)<q j ∧ q j≤S.card ∧ (q (j+1):ℝ)≤g*q j)
    (hfresh : ∀(j : ℕ) (hj : j<l) (a : ℕ), (1-30*g)*μ≤signedFreshCoordinate data S
      (walkDifferenceLaw (fun t => z (a+t)) (length j))
      (fun ij => z (a+ij.1.val)) (fun ij => z (a+ij.2.val)) (q (j+1))
      (by have := hm j hj; omega))
    (hcost : ∀j<l, 2*Real.log (wordStepBall b e (D*length j)).card≤8*g*q j*μ)
    (hsuffix : Real.log (wordStepBall b e (D*K.bound)).card≤err*(q l:ℝ)*μ) :
    (1-(1/2:ℝ)^l-40*g-err)*(q l:ℝ)*μ≤
      signedPointEntropy data S ((P.run z length l).advance K).law
        (fun a => z a.val) (q l) := by
  have h1 := P.run_entropy data S hS b e z hD hs hg hg1 hμ length q l hm hfresh hcost
  have h2 := (P.run z length l).advance_entropy K data S hS b e z hD hs (q l)
  nlinarith only [h1,h2,hsuffix]

lemma signedPointEntropy_exact_start (data : SignedResidueData L) (S : Finset ℕ)
    (K : ForwardKernel) (z : ℕ → L) (a s : ℕ) :
    signedPointEntropy data S ((TimeLaw.at a).advance K).law (fun t => z t.val) s=
      signedPointEntropy data S (K.law a) (fun t => z (a+t.val)) s := by
  rw [TimeLaw.at_advance]
  change signedPointEntropy data S ((K.law a).map
    (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1)))) (fun t => z t.val) s=_
  rw [signedPointEntropy_map]
  rfl

end Entry002
