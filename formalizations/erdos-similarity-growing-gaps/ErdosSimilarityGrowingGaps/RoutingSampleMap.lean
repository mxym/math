import ErdosSimilarityGrowingGaps.GreedySampling
import ErdosSimilarityGrowingGaps.RoutingTreeBounds
import ErdosSimilarityGrowingGaps.RoutingPreorder
import ErdosSimilarityGrowingGaps.RoutingSchedule
import ErdosSimilarityGrowingGaps.SequenceTransfer

namespace ErdosSimilarityGrowingGaps

open Set

/-!
Finite sample maps for a scheduled routing tree.

`routingSampleIndex` chooses the first logarithmic sample at an edge's integer
left endpoint.  The two hypotheses `D ≤ baseLength` and `D < baseLength` are
kept explicit: they are exactly the interior-width and separation budgets
needed to turn annular filling into a finite, injective sample map.
-/

noncomputable def routingSampleIndex (Z : LogScale) {M d : ℕ}
    (c : RoutingTemplate M d) (D : ℝ) (e : RoutingEdge M d) : ℕ :=
  firstGeIndex Z (c.edgeStart e)

/-- Every edge sample lies in the edge's `D`-buffer. -/
theorem routingSampleIndex_bounds
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D ≤ c.baseLength) (e : RoutingEdge M d) :
    (c.edgeStart e : ℝ) ≤ Z.z (routingSampleIndex Z c D e) ∧
      Z.z (routingSampleIndex Z c D e) ≤ (c.edgeStart e : ℝ) + D := by
  have hlen : 0 < c.edgeLength e :=
    RoutingTemplate.length_positive M c.gap c.baseLength (d - e.1.1.val) hM hL
  have hstart_nat := c.edgeStart_ge_origin e
  have hstart : (c.origin : ℝ) ≤ (c.edgeStart e : ℝ) := by
    exact_mod_cast hstart_nat
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlow : (c.origin : ℝ) / R ≤ (c.edgeStart e : ℝ) := by
    have ho : 0 ≤ (c.origin : ℝ) := by
      exact_mod_cast (Nat.zero_le c.origin)
    have hdiv : (c.origin : ℝ) / R ≤ c.origin := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < R)]
      nlinarith
    exact hdiv.trans hstart
  have hbase : c.baseLength ≤ c.edgeLength e :=
    RoutingTemplate.base_le_length M c.gap c.baseLength _ hM
  have hbase' : (c.baseLength : ℝ) ≤ (c.edgeLength e : ℝ) := by
    exact_mod_cast hbase
  have hDlen : D ≤ (c.edgeLength e : ℝ) := hD.trans hbase'
  have hendcast : (c.edgeStart e : ℝ) + (c.edgeLength e : ℝ) =
      (c.edgeEnd e : ℝ) + 1 := by
    unfold RoutingTemplate.edgeEnd
    have hlen' : 1 ≤ c.edgeLength e := by omega
    rw [Nat.cast_sub (by omega : 1 ≤ c.edgeStart e + c.edgeLength e)]
    push_cast
    linarith
  have hend := (c.edgeEnd_within_total hM hL e).2
  have hend' : (c.edgeEnd e : ℝ) + 1 ≤
      (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
    exact_mod_cast hend
  have htop : (c.edgeStart e : ℝ) + D ≤ R * (c.origin : ℝ) := by
    have hleft : (c.edgeStart e : ℝ) + D ≤
        (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
      linarith [hend', hDlen, hendcast]
    have hspan' : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ c.origin := by
      exact_mod_cast hspan
    have hRmul : (c.origin : ℝ) + (c.origin : ℝ) ≤ R * (c.origin : ℝ) := by
      have ho : 0 ≤ (c.origin : ℝ) := by positivity
      nlinarith
    linarith
  obtain ⟨n, hnlo, hnhi⟩ := hfill.sample_mem hlow htop
  have hi := firstGeIndex_value_le_of_mem Z (c.edgeStart e) D n ⟨hnlo, hnhi⟩
  exact ⟨(firstGeIndex_spec Z (c.edgeStart e)).1, hi⟩

/-! The next two lemmas isolate the deterministic point-transfer estimate.
    Unlike `FillsAnnulus.sample_powerPoint_error`, they apply to a *specified*
    sample index once its logarithmic coordinate is known to lie in the
    interval.  This is the estimate needed by the first-ge sample map. -/

theorem powerPoint_error_of_z_bounds
    {Z : LogScale} {K : ℕ} {x : ℝ}
    {p : PowerParams (1 / (K : ℝ)) K} {n : ℕ}
    {v D C : ℝ} (hK : 2 ≤ K) (hD : 0 ≤ D)
    (hlo : v ≤ Z.z n) (hhi : Z.z n ≤ v + D) (_hC : 0 ≤ C) :
    |powerPoint (input Z n) C (x, p) -
        powerPoint ((2 : ℝ) ^ (-v)) C (x, p)| ≤
      |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
        (2 : ℝ) ^ (-(v + D) * p.1.1)) := by
  have hs : 0 < p.1.1 := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    exact lt_of_lt_of_le (by positivity) p.1.2.1
  have hlow : (2 : ℝ) ^ (-(v + D)) ≤ input Z n := by
    rw [input_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hhigh : input Z n ≤ (2 : ℝ) ^ (-v) := by
    rw [input_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hpowlow : (2 : ℝ) ^ (-(v + D) * p.1.1) ≤
      (input Z n) ^ p.1.1 := by
    calc
      (2 : ℝ) ^ (-(v + D) * p.1.1) =
          ((2 : ℝ) ^ (-(v + D))) ^ p.1.1 :=
        Real.rpow_mul (by norm_num) _ _
      _ ≤ (input Z n) ^ p.1.1 :=
        Real.rpow_le_rpow (by positivity) hlow hs.le
  have hpowhigh : (input Z n) ^ p.1.1 ≤
      (2 : ℝ) ^ (-v * p.1.1) := by
    calc
      (input Z n) ^ p.1.1 ≤ ((2 : ℝ) ^ (-v)) ^ p.1.1 :=
        Real.rpow_le_rpow (input_pos Z n).le hhigh hs.le
      _ = (2 : ℝ) ^ (-v * p.1.1) :=
        (Real.rpow_mul (by norm_num) _ _).symm
  have hwidth : 0 ≤ (2 : ℝ) ^ (-v * p.1.1) -
      (2 : ℝ) ^ (-(v + D) * p.1.1) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have habs : |(input Z n) ^ p.1.1 -
      (2 : ℝ) ^ (-v * p.1.1)| ≤
      (2 : ℝ) ^ (-v * p.1.1) -
        (2 : ℝ) ^ (-(v + D) * p.1.1) := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |powerPoint (input Z n) C (x, p) -
        powerPoint ((2 : ℝ) ^ (-v)) C (x, p)| =
      |p.2.1 * C * (input Z n) ^ p.1.1 -
        p.2.1 * C * ((2 : ℝ) ^ (-v)) ^ p.1.1| := by
          simp only [powerPoint]
          ring_nf
    _ = |p.2.1 * C * (input Z n) ^ p.1.1 -
        p.2.1 * C * (2 : ℝ) ^ (-v * p.1.1)| := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _]
    _ ≤ |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
        (2 : ℝ) ^ (-(v + D) * p.1.1)) := by
      rw [show p.2.1 * C * (input Z n) ^ p.1.1 -
          p.2.1 * C * (2 : ℝ) ^ (-v * p.1.1) =
            p.2.1 * C * ((input Z n) ^ p.1.1 -
              (2 : ℝ) ^ (-v * p.1.1)) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)

theorem powerPoint_mem_thickening_of_z_bounds
    {Z : LogScale} {K : ℕ} {x : ℝ}
    {p : PowerParams (1 / (K : ℝ)) K} {n : ℕ}
    {v D C r : ℝ} (hK : 2 ≤ K) (hD : 0 ≤ D)
    (hlo : v ≤ Z.z n) (hhi : Z.z n ≤ v + D) (hC : 0 ≤ C)
    {G : Set ℝ}
    (hideal : powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ∈ G)
    (hwidth : |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
      (2 : ℝ) ^ (-(v + D) * p.1.1)) < r) :
    powerPoint (input Z n) C (x, p) ∈ Metric.thickening r G := by
  apply Metric.mem_thickening_iff.2
  refine ⟨powerPoint ((2 : ℝ) ^ (-v)) C (x, p), hideal, ?_⟩
  rw [Real.dist_eq]
  exact (powerPoint_error_of_z_bounds hK hD hlo hhi hC).trans_lt hwidth

/-- Samples chosen independently at distinct edges remain distinct when the
annular width is strictly smaller than the base edge length. -/
theorem routingSampleIndex_injective
    {Z : LogScale} {M d : ℕ} {ι : Type*} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D < c.baseLength) (edges : ι → RoutingEdge M d)
    (hstart : Function.Injective (fun i => c.edgeStart (edges i)))
    (hsep : ∀ i j, c.edgeStart (edges i) < c.edgeStart (edges j) →
      c.edgeEnd (edges i) + 1 ≤ c.edgeStart (edges j)) :
    Function.Injective (fun i => routingSampleIndex Z c D (edges i)) := by
  intro i j hij
  by_contra hne
  have hstarts : c.edgeStart (edges i) ≠ c.edgeStart (edges j) := by
    intro heq
    exact hne (hstart heq)
  rcases lt_or_gt_of_ne hstarts with hlt | hgt
  · have hsep := hsep i j hlt
    have hbi := routingSampleIndex_bounds c hM hL hspan hR hfill hD.le (edges i)
    have hbj := routingSampleIndex_bounds c hM hL hspan hR hfill hD.le (edges j)
    have hbase : c.baseLength ≤ c.edgeLength (edges i) :=
      RoutingTemplate.base_le_length M c.gap c.baseLength _ hM
    have hstrict : (c.edgeStart (edges i) : ℝ) + D <
        (c.edgeEnd (edges i) : ℝ) + 1 := by
      have hlen : 0 < c.edgeLength (edges i) :=
        RoutingTemplate.length_positive M c.gap c.baseLength _ hM hL
      have hcast : (c.edgeStart (edges i) : ℝ) + (c.edgeLength (edges i) : ℝ) =
          (c.edgeEnd (edges i) : ℝ) + 1 := by
        unfold RoutingTemplate.edgeEnd
        have hlen' : 1 ≤ c.edgeLength (edges i) := by omega
        rw [Nat.cast_sub (by omega : 1 ≤ c.edgeStart (edges i) + c.edgeLength (edges i))]
        push_cast
        linarith
      have hbase' : (c.baseLength : ℝ) ≤ (c.edgeLength (edges i) : ℝ) := by
        exact_mod_cast hbase
      have hDlen : D < (c.edgeLength (edges i) : ℝ) := lt_of_lt_of_le hD hbase'
      linarith [hcast]
    have hsep' : (c.edgeEnd (edges i) : ℝ) + 1 ≤
        (c.edgeStart (edges j) : ℝ) := by
      exact_mod_cast hsep
    have hz : Z.z (routingSampleIndex Z c D (edges i)) <
        Z.z (routingSampleIndex Z c D (edges j)) := by
      linarith [hbi.2, hbj.1, hstrict, hsep']
    have hn : routingSampleIndex Z c D (edges i) <
        routingSampleIndex Z c D (edges j) := (Z.strictMono.lt_iff_lt).mp hz
    exact (Nat.ne_of_lt hn) hij
  · have hsep := hsep j i hgt
    have hbi := routingSampleIndex_bounds c hM hL hspan hR hfill hD.le (edges i)
    have hbj := routingSampleIndex_bounds c hM hL hspan hR hfill hD.le (edges j)
    have hbase : c.baseLength ≤ c.edgeLength (edges j) :=
      RoutingTemplate.base_le_length M c.gap c.baseLength _ hM
    have hstrict : (c.edgeStart (edges j) : ℝ) + D <
        (c.edgeEnd (edges j) : ℝ) + 1 := by
      have hlen : 0 < c.edgeLength (edges j) :=
        RoutingTemplate.length_positive M c.gap c.baseLength _ hM hL
      have hcast : (c.edgeStart (edges j) : ℝ) + (c.edgeLength (edges j) : ℝ) =
          (c.edgeEnd (edges j) : ℝ) + 1 := by
        unfold RoutingTemplate.edgeEnd
        have hlen' : 1 ≤ c.edgeLength (edges j) := by omega
        rw [Nat.cast_sub (by omega : 1 ≤ c.edgeStart (edges j) + c.edgeLength (edges j))]
        push_cast
        linarith
      have hbase' : (c.baseLength : ℝ) ≤ (c.edgeLength (edges j) : ℝ) := by
        exact_mod_cast hbase
      have hDlen : D < (c.edgeLength (edges j) : ℝ) := lt_of_lt_of_le hD hbase'
      linarith [hcast]
    have hsep' : (c.edgeEnd (edges j) : ℝ) + 1 ≤
        (c.edgeStart (edges i) : ℝ) := by
      exact_mod_cast hsep
    have hz : Z.z (routingSampleIndex Z c D (edges j)) <
        Z.z (routingSampleIndex Z c D (edges i)) := by
      linarith [hbi.1, hbj.2, hstrict, hsep']
    have hn := (Z.strictMono.lt_iff_lt).mp hz
    exact (Nat.ne_of_lt hn) hij.symm

/-- A single interior-margin activation transfers through an edge sample.
The margin is strict and therefore handles the open activation endpoints. -/
theorem routingSampleIndex_activation_of_margin
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    {K : ℕ} {D : ℝ} (hD : 0 ≤ D) (e : RoutingEdge M d)
    {k : ℤ} (p : PowerParams (1 / K) K) (hK : 2 ≤ K)
    (hp : p ∈ powerActivation (c.edgeStart e) k
      (c.edgeStart e) ((c.edgeStart e : ℝ) + c.edgeLength e))
    (hsample : (c.edgeStart e : ℝ) ≤ Z.z (routingSampleIndex Z c D e))
    (hsample' : Z.z (routingSampleIndex Z c D e) ≤
      (c.edgeStart e : ℝ) + D)
    (hmargin : p.1.1 * D <
      (c.edgeStart e : ℝ) + c.edgeLength e -
        (p.1.1 * (c.edgeStart e : ℝ) - (k : ℝ))) :
    p ∈ sequenceWindowActivations Z (routingSampleIndex Z c D e) k
      (fun _ : Fin 1 => ((c.edgeStart e : ℝ),
        (c.edgeStart e : ℝ) + c.edgeLength e)) := by
  exact sequence_activation_of_sample_interval
    (windows := fun _ : Fin 1 => ((c.edgeStart e : ℝ),
      (c.edgeStart e : ℝ) + c.edgeLength e)) (e := 0) D p hK hp
    hsample hsample' hmargin

/-- The preceding activation transfer with annular filling supplying the
sample interval bounds. -/
theorem routingSampleIndex_activation_of_filling_margin
    {Z : LogScale} {M d K : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D ≤ c.baseLength) (e : RoutingEdge M d)
    {k : ℤ} (p : PowerParams (1 / (K : ℝ)) K) (hK : 2 ≤ K)
    (hp : p ∈ powerActivation (c.edgeStart e) k
      (c.edgeStart e) ((c.edgeStart e : ℝ) + c.edgeLength e))
    (hmargin : p.1.1 * D <
      (c.edgeStart e : ℝ) + c.edgeLength e -
        (p.1.1 * (c.edgeStart e : ℝ) - (k : ℝ))) :
    p ∈ sequenceWindowActivations Z (routingSampleIndex Z c D e) k
      (fun _ : Fin 1 => ((c.edgeStart e : ℝ),
        (c.edgeStart e : ℝ) + c.edgeLength e)) := by
  obtain ⟨hlo, hhi⟩ := routingSampleIndex_bounds c hM hL hspan hR hfill hD e
  exact routingSampleIndex_activation_of_margin c (by linarith [hfill.2.2.1]) e p hK hp hlo hhi hmargin

/-- Image cardinality is preserved by an injective finite sample map. -/
theorem routingSampleIndex_image_card
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    (D : ℝ) (T : Finset (RoutingEdge M d))
    (hinj : Function.Injective (fun e => routingSampleIndex Z c D e)) :
    (T.image (routingSampleIndex Z c D)).card = T.card := by
  exact Finset.card_image_of_injective T hinj

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

/-- Canonical preorder makes the integer left endpoints of routing edges
pairwise distinct. -/
theorem routingEdge_edgeStart_injective
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength) :
    Function.Injective c.edgeStart := by
  intro e f heq
  obtain ⟨i, hi⟩ := (preorderWindowPath_complete M d _).1
    (routingEdge_mem_preorderPaths e)
  obtain ⟨j, hj⟩ := (preorderWindowPath_complete M d _).1
    (routingEdge_mem_preorderPaths f)
  have hstart : RoutingTemplate.incomingStart M c.gap c.baseLength d c.origin
      (preorderWindowPath i) =
      RoutingTemplate.incomingStart M c.gap c.baseLength d c.origin
      (preorderWindowPath j) := by
    simpa only [hi, hj, RoutingTemplate.incomingStart_of_edge] using heq
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs := (preorderPaths_pairwise_starts M c.gap c.baseLength d c.origin
        hM hL).rel_get_of_lt hlt
      exact (Nat.ne_of_lt hs) hstart
    · have hs := (preorderPaths_pairwise_starts M c.gap c.baseLength d c.origin
        hM hL).rel_get_of_lt hgt
      exact (Nat.ne_of_lt hs) hstart.symm
  have hpath : List.ofFn e.1.2 ++ [e.2] =
      List.ofFn f.1.2 ++ [f.2] := by
    rw [← hi, ← hj, hij]
  have hlen : (List.ofFn e.1.2).length =
      (List.ofFn f.1.2).length := by
    have hh := congrArg List.length hpath
    simpa using hh
  cases e with
  | mk ev ec =>
    cases f with
    | mk fv fc =>
      cases ev with
      | mk evn evf =>
        cases fv with
        | mk fvn fvf =>
          dsimp at hpath hlen ⊢
          have hv : evn = fvn := by
            apply Fin.ext
            simpa using hlen
          cases hv
          obtain ⟨hleft, hright⟩ := List.append_inj hpath hlen
          have hfun : evf = fvf := List.ofFn_injective hleft
          have hfc : ec = fc := by simpa using List.cons.inj hright
          cases hfun
          cases hfc
          rfl



/-- The previous finite-map theorem specializes directly to the complete
routing edge type; no enumeration choice is needed for injectivity. -/
theorem routingSampleIndex_all_edges_injective
    {Z : LogScale} {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 1 ≤ M) (hL : 0 < c.baseLength)
    (hspan : RoutingTemplate.span M c.gap c.baseLength d ≤ c.origin)
    {R D : ℝ} (hR : 2 ≤ R)
    (hfill : FillsAnnulus Z (c.origin : ℝ) R D)
    (hD : D < c.baseLength) :
    Function.Injective (routingSampleIndex Z c D) := by
  have h := routingSampleIndex_injective c hM hL hspan hR hfill hD
      (fun e : RoutingEdge M d => e)
      (routingEdge_edgeStart_injective c hM hL)
      (by
        intro e f hlt
        have hs := c.earlier_edgeEnd_add_gap_le hM hL e f hlt
        omega)
  simpa only [id_eq] using h

end ErdosSimilarityGrowingGaps
