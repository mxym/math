import ContinuumRemainder.Counting
import ContinuumRemainder.LogRoutingProbability
import ContinuumGeometric.RoutingLocalProbability

namespace ContinuumRemainder
open ContinuumGeometric Set
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable def sampleVertexPairs {A : Set ℝ} {s₀ : ℝ} {h M d : ℕ}
    (C : SampledLogConfiguration A s₀ h) (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₁ : ℝ) (k : ℤ) : Finset (Fin (M-1) × ℕ) :=
  C.potentialPairs s₁ c.origin (RoutingTemplate.span M c.gap c.baseLength d) k
    (fun i=>((vertexWindowStart c v i:ℝ),
      (vertexWindowStart c v i:ℝ)+vertexWindowLength c v))

theorem sampleVertexPairs_card_le {A : Set ℝ} {s₀ : ℝ} {h M d : ℕ}
    (C : SampledLogConfiguration A s₀ h) (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₁ : ℝ) (k : ℤ) :
    (sampleVertexPairs C c v s₁ k).card ≤
      (M-1)*candidateLabelBudget c.origin (RoutingTemplate.span M c.gap c.baseLength d) k :=
  C.potentialPairs_card_le s₁ _ _ k _

theorem sample_vertex_output_separation {A : Set ℝ} {s₀ : ℝ} {h M d : ℕ}
    (C : SampledLogConfiguration A s₀ h) (hs₀ : 0<s₀) (c : RoutingTemplate M d)
    (v : InternalNode M d) (s₁ : ℝ) (k : ℤ) (r : PowerParams s₀ s₁) :
    let pairs:=sampleVertexPairs C c v s₁ k
    ∀ i j : Fin pairs.card, i≠j → candidatePairEdge pairs i=candidatePairEdge pairs j →
      3≤|r.1.1*C.z (candidatePairIndex pairs j)-r.1.1*C.z (candidatePairIndex pairs i)| := by
  dsimp only
  let pairs:=sampleVertexPairs C c v s₁ k
  intro i j hij hc
  have hn : candidatePairIndex pairs i≠candidatePairIndex pairs j := by
    intro hh
    exact hij (candidatePairEnumeration_injective pairs (Prod.ext hc hh))
  rcases lt_or_gt_of_ne hn with hh|hh
  · have hg:=C.output_gap_of_lt hs₀ r.1.1 r.1.2.1 _ _ hh
    exact hg.trans (le_abs_self _)
  · have hg:=C.output_gap_of_lt hs₀ r.1.1 r.1.2.1 _ _ hh
    calc
      3≤r.1.1*C.z (candidatePairIndex pairs i)-r.1.1*C.z (candidatePairIndex pairs j) := hg
      _ ≤ |r.1.1*C.z (candidatePairIndex pairs i)-r.1.1*C.z (candidatePairIndex pairs j)| := le_abs_self _
      _ = _ := abs_sub_comm _ _

theorem sample_vertex_active_count {A : Set ℝ} {s₀ : ℝ} {h M d : ℕ}
    (C : SampledLogConfiguration A s₀ h) (hs₀ : 0<s₀) (c : RoutingTemplate M d)
    (hM : 0<M) (hL : 0<c.baseLength) (v : InternalNode M d) (s₁ : ℝ) (k : ℤ)
    (hell : 2*(s₁*C.B)≤vertexWindowLength c v)
    (hstart : s₁*C.z 0-k≤c.origin) (r : PowerParams s₀ s₁) :
    let pairs:=sampleVertexPairs C c v s₁ k
    (1/(2*(s₁*C.B)))*((M:ℝ)-1)*vertexWindowLength c v ≤
      (logActiveLocalCandidates c v (candidatePairEdge pairs)
        (fun i=>C.z (candidatePairIndex pairs i)) k r).card := by
  dsimp only
  let pairs:=sampleVertexPairs C c v s₁ k
  have hv : ∀ i : Fin (M-1), (vertexWindowStart c v i:ℝ)+vertexWindowLength c v≤
      (c.origin:ℝ)+RoutingTemplate.span M c.gap c.baseLength d := by
    intro i
    have hh:=(c.edgeEnd_within_total hM hL (RoutingTemplate.selectorRoutingEdge ⟨v,i⟩)).2
    have hl:=RoutingTemplate.length_positive M c.gap c.baseLength (d-v.1.val) hM hL
    have hn : vertexWindowStart c v i+vertexWindowLength c v≤
        c.origin+RoutingTemplate.span M c.gap c.baseLength d := by
      simp only [RoutingTemplate.edgeEnd,RoutingTemplate.edgeLength,
        RoutingTemplate.selectorRoutingEdge] at hh
      change c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v,i⟩)+
        RoutingTemplate.lengthAt M c.gap c.baseLength (d-v.1.val)≤_ 
      simp only [RoutingTemplate.selectorRoutingEdge]
      omega
    exact_mod_cast hn
  have hs : ∀ i : Fin (M-1), s₁*C.z 0-k≤(vertexWindowStart c v i:ℝ) := by
    intro i
    exact hstart.trans (by exact_mod_cast c.edgeStart_ge_origin (RoutingTemplate.selectorRoutingEdge ⟨v,i⟩))
  have hm:=(C.potentialPairs_active_count hs₀ s₁ c.origin
    (RoutingTemplate.span M c.gap c.baseLength d) (fun i=>(vertexWindowStart c v i:ℝ))
    (vertexWindowLength c v) k hell hv hs r).1
  have he : (logActiveLocalCandidates c v (candidatePairEdge pairs)
      (fun i=>C.z (candidatePairIndex pairs i)) k r).card=
    (pairs.filter fun q=>r∈logActivation (C.z q.2) k (vertexWindowStart c v q.1)
      ((vertexWindowStart c v q.1:ℝ)+vertexWindowLength c v)).card := by
    simpa only [logActiveLocalCandidates,vertexWindowStart,vertexWindowLength,
      RoutingTemplate.edgeLength,RoutingTemplate.selectorRoutingEdge] using
      candidatePair_active_card pairs (fun q=>r∈logActivation (C.z q.2) k
        (vertexWindowStart c v q.1) ((vertexWindowStart c v q.1:ℝ)+vertexWindowLength c v))
  rw [he]
  have hM₁ : 1≤M := hM
  have hc : ((M-1:ℕ):ℝ)=(M:ℝ)-1 := by rw [Nat.cast_sub hM₁]; norm_num
  have heL : (1/(2*(s₁*C.B)))*((M:ℝ)-1)*vertexWindowLength c v =
      ((M-1:ℕ):ℝ)*((vertexWindowLength c v:ℝ)/(2*(s₁*C.B))) := by rw [hc]; ring
  rw [heL]
  exact hm

theorem sample_vertex_continuum_joint_miss_bound {A : Set ℝ} {s₀ : ℝ} {h M d : ℕ}
    (C : SampledLogConfiguration A s₀ h) (hs₀ : 0<s₀) (c : RoutingTemplate M d)
    (hM : 0<M) (hd : 0<d) (hL : 0<c.baseLength) (hU : 4≤c.origin)
    (p s₁ x : ℝ) (hp₀ : 0≤p) (hp₁ : p≤1) (hs : s₀≤s₁) (k : ℤ)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (hell : 2*(s₁*C.B)≤vertexWindowLength c v) (hstart : s₁*C.z 0-k≤c.origin)
    (hbudget :
      ((20*((sampleVertexPairs C c v s₁ k).card*(3+2^(2*vertexWindowLength c v+3))+5)^2:ℕ):ℝ)*
        Real.exp (-(p*(1/(2*(s₁*C.B)))*((M:ℝ)-1)/2)*vertexWindowLength c v)≤p) :
    let pairs:=sampleVertexPairs C c v s₁ k
    tableProbability p (fun ω=>centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁, logLocalAllMiss c hM hd s₀ s₁ x k
        (fun i=>⟨v,candidatePairEdge pairs i⟩)
        (fun i=>C.z (candidatePairIndex pairs i)) r ω)≤
      tableProbability (T:=TerminalAddress c hd) p
        (fun ω=>centerExposureAtom (actualCenterExposure c x bits) ω.selectors)*p := by
  dsimp only
  let pairs:=sampleVertexPairs C c v s₁ k
  have hb:=log_continuum_joint_miss_bound c hM hd hL hU p s₀ s₁ x
    (1/(2*(s₁*C.B))) hp₀ hp₁ hs k bits v (candidatePairEdge pairs)
    (fun i=>C.z (candidatePairIndex pairs i))
    (fun r=>sample_vertex_output_separation C hs₀ c v s₁ k r)
    (vertexWindowLength c v) (fun _=>rfl)
    (fun r=>sample_vertex_active_count C hs₀ c hM hL v s₁ k hell hstart r)
  apply hb.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hbudget (tableProbability_nonneg p hp₀ hp₁ _)

end ContinuumRemainder
