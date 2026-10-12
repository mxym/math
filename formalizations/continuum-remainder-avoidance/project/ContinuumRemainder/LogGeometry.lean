import ContinuumGeometric.RoutingActiveGeometry
import ContinuumGeometric.RoutingStableGeometry

namespace ContinuumRemainder

open ContinuumGeometric Set

noncomputable def logInput (z : ℝ) : ℝ := (2 : ℝ) ^ (-z)

def logActivation (z : ℝ) (k : ℤ) (u v : ℝ) {s₀ s₁ : ℝ} :
    Set (PowerParams s₀ s₁) := {p | u < p.1.1 * z - k ∧ p.1.1 * z - k < v}

noncomputable def logPoint (z : ℝ) (k : ℤ) {s₀ s₁ : ℝ}
    (xp : ℝ × PowerParams s₀ s₁) : ℝ :=
  powerPoint (logInput z) ((2 : ℝ) ^ k) xp

theorem logInput_pos (z : ℝ) : 0 < logInput z :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem continuous_logPoint (z : ℝ) (k : ℤ) (s₀ s₁ : ℝ) :
    Continuous (logPoint z k : ℝ × PowerParams s₀ s₁ → ℝ) :=
  continuous_powerPoint s₀ s₁ (logInput z) ((2 : ℝ) ^ k) (logInput_pos z).ne'

theorem isOpen_logActivation (z : ℝ) (k : ℤ) (u v : ℝ) (s₀ s₁ : ℝ) :
    IsOpen (logActivation z k u v : Set (PowerParams s₀ s₁)) := by
  have hc : Continuous (fun p : PowerParams s₀ s₁ => p.1.1 * z - k) :=
    ((continuous_subtype_val.comp continuous_fst).mul_const z).sub continuous_const
  exact (isOpen_Ioo.preimage hc)

theorem log_offset (z s t : ℝ) (k : ℤ) :
    t * (2 : ℝ) ^ k * (logInput z) ^ s =
      t * (2 : ℝ) ^ ((k : ℝ) - s * z) := by
  unfold logInput
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_intCast,
    mul_assoc, ← Real.rpow_add (by norm_num)]
  congr 2
  ring

theorem log_point_range (s₀ s₁ x u v z : ℝ) (k : ℤ)
    (p : PowerParams s₀ s₁) (ha : p ∈ logActivation z k u v) :
    x < logPoint z k (x,p) ∧ logPoint z k (x,p) < x + (2 : ℝ) ^ (1-u) := by
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) p.2.2.1
  have hh : (2:ℝ)^((k:ℝ)-p.1.1*z) < (2:ℝ)^(-u) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [ha.1])
  have hpos : 0 < p.2.1 * (2:ℝ)^((k:ℝ)-p.1.1*z) :=
    mul_pos ht (Real.rpow_pos_of_pos (by norm_num) _)
  have hb : p.2.1 * (2:ℝ)^((k:ℝ)-p.1.1*z) < (2:ℝ)^(1-u) := by
    calc
      _ ≤ 2*(2:ℝ)^((k:ℝ)-p.1.1*z) :=
        mul_le_mul_of_nonneg_right p.2.2.2 (Real.rpow_pos_of_pos (by norm_num) _).le
      _ < 2*(2:ℝ)^(-u) := mul_lt_mul_of_pos_left hh (by norm_num)
      _ = (2:ℝ)^(1-u) := by rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  simpa only [logPoint,powerPoint,log_offset] using
    (show x<x+p.2.1*(2:ℝ)^((k:ℝ)-p.1.1*z) ∧
      x+p.2.1*(2:ℝ)^((k:ℝ)-p.1.1*z)<x+(2:ℝ)^(1-u) from
      ⟨by linarith,by linarith⟩)

theorem log_offset_lower (s₀ s₁ x u v z : ℝ) (k : ℤ)
    (p : PowerParams s₀ s₁) (ha : p ∈ logActivation z k u v) :
    (2:ℝ)^(-v) < logPoint z k (x,p)-x := by
  have hh : (2:ℝ)^(-v) < (2:ℝ)^((k:ℝ)-p.1.1*z) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [ha.2])
  have hm : (2:ℝ)^((k:ℝ)-p.1.1*z) ≤ p.2.1*(2:ℝ)^((k:ℝ)-p.1.1*z) := by
    nlinarith [p.2.2.1,Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((k:ℝ)-p.1.1*z)]
  simpa only [logPoint,powerPoint,log_offset,add_sub_cancel_left] using hh.trans_le hm

theorem log_point_short (s₀ s₁ x z : ℝ) (u ell : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (p : PowerParams s₀ s₁)
    (ha : p ∈ logActivation z k u ((u:ℝ)+ell)) :
    x<logPoint z k (x,p) ∧ logPoint z k (x,p)-x<1/8 := by
  have hr:=log_point_range s₀ s₁ x u ((u:ℝ)+ell) z k p ha
  have hur : (4:ℝ)≤u := by exact_mod_cast hu
  have hh : (2:ℝ)^(1-(u:ℝ))≤(2:ℝ)^(-3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  norm_num at hh
  exact ⟨hr.1,by linarith [hr.2]⟩

theorem log_gridAddress_ne_center (s₀ s₁ x z : ℝ) (u ell : ℕ) (k : ℤ)
    (hu : 4 ≤ u) (hell : 0<ell) (p : PowerParams s₀ s₁)
    (ha : p∈logActivation z k u ((u:ℝ)+ell)) :
    gridAddress (u+ell-1) (logPoint z k (x,p))≠gridAddress (u+ell-1) x := by
  have hl:=log_offset_lower s₀ s₁ x u ((u:ℝ)+ell) z k p ha
  have hs:=log_point_short s₀ s₁ x z u ell k hu p ha
  have hn : (0:ℝ)<((2^(u+ell-1+3):ℕ):ℝ) := by positivity
  have hm:=mul_lt_mul_of_pos_left hl hn
  rw [active_window_grid_scale u ell hell] at hm
  exact (gridAddress_ne_of_scaled_small_gap _ x (logPoint z k (x,p))
    (by linarith) hs.2.le).symm

theorem log_offset_ratio (s₀ s₁ x z z' : ℝ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hgap : 3≤p.1.1*z'-p.1.1*z) :
    8*(logPoint z' k (x,p)-x)≤logPoint z k (x,p)-x := by
  have hh : (2:ℝ)^(((k:ℝ)-p.1.1*z')+3)≤(2:ℝ)^((k:ℝ)-p.1.1*z) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_add (by norm_num)] at hh
  norm_num at hh
  have ht : (0:ℝ)≤p.2.1 := by linarith [p.2.2.1]
  have hm:=mul_le_mul_of_nonneg_left hh ht
  simp only [logPoint,powerPoint,log_offset,add_sub_cancel_left]
  nlinarith [hm]

theorem log_gridAddress_ne_of_output_gap (s₀ s₁ x z z' : ℝ)
    (u ell : ℕ) (k : ℤ) (hu : 4≤u) (hell : 0<ell)
    (p : PowerParams s₀ s₁) (hgap : 3≤p.1.1*z'-p.1.1*z)
    (ha : p∈logActivation z k u ((u:ℝ)+ell))
    (ha' : p∈logActivation z' k u ((u:ℝ)+ell)) :
    gridAddress (u+ell-1) (logPoint z k (x,p))≠
      gridAddress (u+ell-1) (logPoint z' k (x,p)) := by
  have hr:=log_offset_ratio s₀ s₁ x z z' k p hgap
  have hl:=log_offset_lower s₀ s₁ x u ((u:ℝ)+ell) z' k p ha'
  have hs:=log_point_short s₀ s₁ x z u ell k hu p ha
  have hs':=log_point_short s₀ s₁ x z' u ell k hu p ha'
  have hn : (0:ℝ)<((2^(u+ell-1+3):ℕ):ℝ) := by positivity
  have hm:=mul_lt_mul_of_pos_left (show 7*(2:ℝ)^(-((u:ℝ)+ell))<
    logPoint z k (x,p)-logPoint z' k (x,p) by linarith) hn
  have he : ((2^(u+ell-1+3):ℕ):ℝ)*(7*(2:ℝ)^(-((u:ℝ)+ell)))=28 := by
    calc
      _ = 7*(((2^(u+ell-1+3):ℕ):ℝ)*(2:ℝ)^(-((u:ℝ)+ell))) := by ring
      _ = 28 := by rw [active_window_grid_scale u ell hell]; norm_num
  rw [he] at hm
  exact (gridAddress_ne_of_scaled_small_gap _ (logPoint z' k (x,p))
    (logPoint z k (x,p)) (by linarith) (by linarith)).symm

theorem log_preceding_gridAddress_eq (s₀ s₁ x z : ℝ)
    (u ell b₀ g : ℕ) (k : ℤ) (hu : u=b₀+g+1)
    (p : PowerParams s₀ s₁) (ha : p∈logActivation z k u ((u:ℝ)+ell))
    (hs : NoGridBoundary (2^(b₀+3)) x (2^(-((b₀:ℝ)+g)))) :
    gridAddress b₀ (logPoint z k (x,p))=gridAddress b₀ x := by
  apply (gridAddress_eq_iff _ _ _).2
  apply periodicGridKey_eq_of_no_boundary _ (by positivity) x _ _ ?_ hs
  have hr:=log_point_range s₀ s₁ x u ((u:ℝ)+ell) z k p ha
  have he : (1:ℝ)-u=-((b₀:ℝ)+g) := by rw [hu]; push_cast; ring
  rw [he] at hr
  exact ⟨hr.1.le,hr.2.le⟩

theorem log_stable_earlier_address_agreement {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0<M) (hL : 0<c.baseLength) (hU : c.gap+1≤c.origin)
    (s₀ s₁ x z : ℝ) (k : ℤ) (e : SelectorEdge M d)
    (p : PowerParams s₀ s₁) (hx : x∈actualStableCenters c)
    (ha : p∈logActivation z k (c.edgeStart (RoutingTemplate.selectorRoutingEdge e))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge e):ℝ)+
        c.edgeLength (RoutingTemplate.selectorRoutingEdge e))) :
    EarlierAddressAgreement c x (logPoint z k (x,p)) e := by
  intro f hf
  have hb:=c.earlier_edgeEnd_le_predecessorBoundary hM hL
    (RoutingTemplate.selectorRoutingEdge f) (RoutingTemplate.selectorRoutingEdge e) hf
  apply dyadic_grid_eq_of_finer_eq _ _ hb _ _
  apply log_preceding_gridAddress_eq s₀ s₁ x z _ _ _ c.gap k
    (c.predecessorBoundary_start hU _) p ha
  simpa only [stableDyadicRadius_eq_rpow] using hx (RoutingTemplate.selectorRoutingEdge e)

theorem log_stable_local_success_mem_routedSet {M d : ℕ}
    (c : RoutingTemplate M d) (hM : 0<M) (hd : 0<d) (hL : 0<c.baseLength)
    (hU : c.gap+1≤c.origin) (s₀ s₁ x z : ℝ) (k : ℤ) (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd))
    (bits : SelectorEdge M d → Bool)
    (hσ : centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
    (v : InternalNode M d) (child : Fin (M-1))
    (hp : (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM ω.selectors x)))
    (hdefault : ∀ i : Fin (M-1),bits ⟨v,i⟩=false) (hx : x∈actualStableCenters c)
    (ha : p∈logActivation z k (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,child⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,child⟩):ℝ)+
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v,child⟩)))
    (hsuccess : ω.selectors (selectorAddress c ⟨v,child⟩ (logPoint z k (x,p)))=true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v,child⟩ (logPoint z k (x,p)))=true) :
    logPoint z k (x,p)∈routedSet c hM hd ω :=
  actual_local_success_mem_routedSet c hM hd hL ω x _ bits hσ v child hp hdefault
    (log_stable_earlier_address_agreement c hM hL hU s₀ s₁ x z k ⟨v,child⟩ p hx ha) hsuccess

end ContinuumRemainder
