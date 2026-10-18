import OperationalCompletion.ReservedLaws
import OperationalCompletion.CapacityConverse
import OperationalCompletion.NaturalRates

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

/-- The one-dimensional Bell target is the identity, including its normalization. -/
theorem bellProjector_one : Extraction.bellProjector (d:=Fin 1) = 1 := by
  have ht := (Extraction.bellProjector_density (d:=Fin 1)).2
  ext ⟨i,j⟩ ⟨r,s⟩
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s
  simpa [Matrix.trace,Fintype.sum_prod_type,Fin.sum_univ_succ,Extraction.bellProjector] using ht

/-- Every trace-preserving actual protocol has exact fidelity at target K=1. -/
theorem protocol_fidelity_one {a b : ℕ} (V : KrausPPTProtocol a b 1)
    (X : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ) (hX : X.trace=1) :
    V.fidelity X=1 := by
  unfold KrausPPTProtocol.fidelity overlap
  rw [bellProjector_one,Matrix.one_mul,Extraction.krausApply_trace V.A V.complete,
    Matrix.trace_mul_cycle]
  have hu : (V.U : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)ᴴ * V.U=1 := V.U.property.1
  rw [hu,Matrix.one_mul,hX]
  rfl

/-- Rates attainable by a genuine sequence of physical protocols in class C. -/
def faithfulAttainableRates (m n : ℕ)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : Set ℝ :=
  {R | 0≤R ∧ ∃ (K : ℕ → ℕ) (hK : ∀ k,0<K k),
    Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R) ∧
    ∃ V : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k),
      (∀ k,C k (K k) (V k)) ∧
      Tendsto (fun k => (V k).fidelity (tensorInput m n k X)) atTop (nhds 1)}

/-- Eventual exactness uses the same physical target and channel sequence. -/
def exactAttainableRates (m n : ℕ)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : Set ℝ :=
  {R | 0≤R ∧ ∃ (K : ℕ → ℕ) (hK : ∀ k,0<K k),
    Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R) ∧
    ∃ V : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k),
      (∀ k,C k (K k) (V k)) ∧
      ∀ᶠ k : ℕ in atTop,(V k).fidelity (tensorInput m n k X)=1}

def faithfulCapacity (m n : ℕ)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : ℝ :=
  sSup (faithfulAttainableRates m n C X)

def exactCapacity (m n : ℕ)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : ℝ :=
  sSup (exactAttainableRates m n C X)

theorem density_entropy_rank_bounds (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    entropy hX.1.isHermitian.eigenvalues≤Real.log X.rank ∧
      Real.log X.rank≤Real.log m+Real.log n := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  have hr : Fintype.card (PositiveSupport p)=X.rank := density_positiveSupport_card_eq_rank X hX.1
  have hH := entropy_le_log_positiveSupport p p hp hs hp hs (fun _ hi => hi)
  rw [hr] at hH
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  have hrpos : 0<X.rank := by rw [←hr]; exact Fintype.card_pos
  have hrD : X.rank≤m*n := by simpa using Matrix.rank_le_card_width X
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hrpos) (show (X.rank:ℝ)≤(m*n:ℕ) by exact_mod_cast hrD)
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast Nat.ne_of_gt hm)
    (by exact_mod_cast Nat.ne_of_gt hn)] at hlog
  exact ⟨hH,hlog⟩

theorem capacityRates_nonneg (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    0≤faithfulRate m n hX.1.isHermitian.eigenvalues ∧ 0≤eventualExactRate m n X := by
  have hb := density_entropy_rank_bounds m n hm hn X hX
  have hm' : 0≤Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  constructor
  · exact le_min hm' (by linarith [hb.1,hb.2])
  · exact le_min hm' (by linarith [hb.2])

theorem csSup_eq_of_initial_interval (S : Set ℝ) (c : ℝ) (hc : 0≤c)
    (hzero : 0∈S) (hu : ∀ r∈S,r≤c) (hl : ∀ r,0≤r → r<c → r∈S) : sSup S=c := by
  have hne : S.Nonempty := ⟨0,hzero⟩
  have hbd : BddAbove S := ⟨c,hu⟩
  have hs0 : 0≤sSup S := le_csSup hbd hzero
  apply le_antisymm (csSup_le hne hu)
  by_contra h
  have hs : sSup S<c := lt_of_not_ge h
  have hm : (sSup S+c)/2∈S := hl _ (by linarith) (by linarith)
  have hh := le_csSup hbd hm
  linarith

theorem exactAttainable_zero (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ k K (hK : 0<K),C k K (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    0∈exactAttainableRates m n C X := by
  refine ⟨le_rfl,(fun _ => 1),(fun _ => by norm_num),?_,
    (fun k => reservedProtocol m n k 1 hm hn hmn (by norm_num)),?_,?_⟩
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
  · exact fun k => hC k 1 (by norm_num)
  · exact Eventually.of_forall (fun k => protocol_fidelity_one _ _ (tensorInput_density m n k X hX).2)

theorem exactAttainable_subset_faithful (m n : ℕ)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    exactAttainableRates m n C X ⊆ faithfulAttainableRates m n C X := by
  rintro R ⟨hR,K,hK,hlim,V,hV,hex⟩
  refine ⟨hR,K,hK,hlim,V,hV,?_⟩
  exact (tendsto_congr' hex).mpr tendsto_const_nhds

theorem faithfulAttainable_le (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (R : ℝ) (hR : R∈faithfulAttainableRates m n C X) :
    R≤faithfulRate m n hX.1.isHermitian.eigenvalues := by
  rcases hR with ⟨_,K,hK,hlim,V,_,hfid⟩
  by_contra h
  have hz := ppt_above_faithful_rate m n hm hn K hK R hlim V X hX (lt_of_not_ge h)
  have hh : (1:ℝ)=0 := tendsto_nhds_unique hfid hz
  norm_num at hh

theorem exactAttainable_le (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (R : ℝ) (hR : R∈exactAttainableRates m n C X) :
    R≤eventualExactRate m n X := by
  rcases hR with ⟨_,K,hK,hlim,V,_,hfid⟩
  by_contra h
  have hz := ppt_above_eventualExact_rate m n hm hn K hK R hlim X hX (lt_of_not_ge h)
  obtain ⟨k,hk,hlt⟩ := (hfid.and hz).exists
  exact (ne_of_lt (hlt (V k))) hk

theorem faithfulAttainable_below (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ k K (hK : 0<K),C k K (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (R : ℝ) (hR : 0≤R) (hbelow : R<faithfulRate m n hX.1.isHermitian.eigenvalues) :
    R∈faithfulAttainableRates m n C X := by
  have hb := lt_min_iff.mp hbelow
  refine ⟨hR,roundedTarget R 0,(fun k => roundedTarget_pos R 0 k),roundedTarget_rate_nonneg R hR,
    (fun k => reservedProtocol m n k (roundedTarget R 0 k) hm hn hmn (roundedTarget_pos R 0 k)),
    (fun k => hC k _ _),?_⟩
  exact reserved_subcritical_rate m n hm hn hmn _ (fun k => roundedTarget_pos R 0 k) R
    (roundedTarget_rate_nonneg R hR) hb.1 X hX (by linarith [hb.2])

theorem exactAttainable_below (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ k K (hK : 0<K),C k K (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (R : ℝ) (hR : 0≤R) (hbelow : R<eventualExactRate m n X) :
    R∈exactAttainableRates m n C X := by
  have hb := lt_min_iff.mp hbelow
  refine ⟨hR,roundedTarget R 0,(fun k => roundedTarget_pos R 0 k),roundedTarget_rate_nonneg R hR,
    (fun k => reservedProtocol m n k (roundedTarget R 0 k) hm hn hmn (roundedTarget_pos R 0 k)),
    (fun k => hC k _ _),?_⟩
  exact reserved_eventually_exact m n hm hn hmn _ (fun k => roundedTarget_pos R 0 k) R
    (roundedTarget_rate_nonneg R hR) hb.1 X hX (by linarith [hb.2])

/-- The capacity is the supremum of actually attainable rates, including the
zero-capacity boundary, for every physical class containing the common family. -/
theorem faithfulCapacity_eq (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ k K (hK : 0<K),C k K (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    faithfulCapacity m n C X=faithfulRate m n hX.1.isHermitian.eigenvalues := by
  apply csSup_eq_of_initial_interval _ _ (capacityRates_nonneg m n hm hn X hX).1
  · exact exactAttainable_subset_faithful m n C X (exactAttainable_zero m n hm hn hmn C hC X hX)
  · exact faithfulAttainable_le m n hm hn C X hX
  · exact fun R hR hb => faithfulAttainable_below m n hm hn hmn C hC X hX R hR hb

/-- The eventual-exact capacity uses a supremum of physical, eventually exact
protocol sequences; no assertion of attainability at the boundary is needed. -/
theorem exactCapacity_eq (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (C : ∀ k K,KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ k K (hK : 0<K),C k K (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    exactCapacity m n C X=eventualExactRate m n X := by
  apply csSup_eq_of_initial_interval _ _ (capacityRates_nonneg m n hm hn X hX).2
  · exact exactAttainable_zero m n hm hn hmn C hC X hX
  · exact exactAttainable_le m n hm hn C X hX
  · exact fun R hR hb => exactAttainable_below m n hm hn hmn C hC X hX R hR hb

theorem productLocal_capacities (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    faithfulCapacity m n (fun _ _ V => V.IsProductLocal) X =
        min (Real.log m) ((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2) ∧
    exactCapacity m n (fun _ _ V => V.IsProductLocal) X =
        min (Real.log m) ((Real.log m+Real.log n-Real.log X.rank)/2) :=
  ⟨faithfulCapacity_eq m n hm hn hmn _ (fun k K hK => reservedProtocol_isProductLocal m n k K hm hn hmn hK) X hX,
   exactCapacity_eq m n hm hn hmn _ (fun k K hK => reservedProtocol_isProductLocal m n k K hm hn hmn hK) X hX⟩

theorem cPPT_capacities (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    faithfulCapacity m n (fun _ _ _ => True) X =
        min (Real.log m) ((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2) ∧
    exactCapacity m n (fun _ _ _ => True) X =
        min (Real.log m) ((Real.log m+Real.log n-Real.log X.rank)/2) :=
  ⟨faithfulCapacity_eq m n hm hn hmn _ (fun _ _ _ => trivial) X hX,
   exactCapacity_eq m n hm hn hmn _ (fun _ _ _ => trivial) X hX⟩

end
end OperationalCompletion
