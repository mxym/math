import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Pairwise resultants over coefficient rings, compatible with specialization
of monic polynomial families even when the specialization creates common roots. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {R S : Type*} [CommRing R] [CommRing S]

def pairwiseResultantsOver : List R[X] → R
  | [] => 1
  | p :: ps => (ps.map fun q => p.resultant q).prod * pairwiseResultantsOver ps

lemma monic_resultant_map [Nontrivial S] (φ : R →+* S)
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) :
    (p.map φ).resultant (q.map φ) = φ (p.resultant q) := by
  rw [hp.natDegree_map φ,hq.natDegree_map φ,Polynomial.resultant_map_map]

/-- Exact specialization identity, without assuming the coefficient homomorphism is injective. -/
theorem pairwiseResultantsOver_map [Nontrivial S] (φ : R →+* S)
    (ps : List R[X]) (hm : ∀ p ∈ ps, p.Monic) :
    pairwiseResultantsOver (ps.map (Polynomial.map φ)) = φ (pairwiseResultantsOver ps) := by
  induction ps with
  | nil => simp [pairwiseResultantsOver]
  | cons p ps ih =>
    have hp := hm p (by simp)
    have ht : ∀ q ∈ ps, q.Monic := fun q hq => hm q (by simp [hq])
    rw [List.map_cons,pairwiseResultantsOver,pairwiseResultantsOver,map_mul,ih ht,map_list_prod]
    congr 1
    rw [List.map_map,List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q hq
    exact monic_resultant_map φ p q hp (ht q hq)

end HydrologyTree
