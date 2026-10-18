import CircuitRecursion.CommutatorError
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Algebra.Group.Subgroup.Lattice

namespace CircuitRecursion

variable {H : Type*} [Group H] {m : ℕ}

/-- Chronological instruction words, matching the circuit convention. -/
def instructionWordValue (G : Fin m → H) : List (Fin m) → H
  | [] => 1
  | i::w => instructionWordValue G w*G i

theorem instructionWordValue_append (G : Fin m → H) (w v : List (Fin m)) :
    instructionWordValue G (w++v)=instructionWordValue G v*instructionWordValue G w := by
  induction w with
  | nil => simp [instructionWordValue]
  | cons i w ih => simp only [List.cons_append,instructionWordValue,ih,mul_assoc]

theorem instructionWordValue_inverse (G : Fin m → H) (inverseLabel : Fin m → Fin m)
    (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹) (w : List (Fin m)) :
    instructionWordValue G (w.reverse.map inverseLabel)=(instructionWordValue G w)⁻¹ := by
  induction w with
  | nil => simp [instructionWordValue]
  | cons i w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      instructionWordValue_append,instructionWordValue,one_mul,ih,hi,mul_inv_rev]

theorem subgroup_instructionWord (G : Fin m → H)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹) (x : H) (hx : x∈Subgroup.closure (Set.range G)) :
    ∃ w : List (Fin m),instructionWordValue G w=x := by
  classical
  let inverseLabel (i : Fin m) := Classical.choose (hinv i)
  have hi : ∀ i,G (inverseLabel i)=(G i)⁻¹ := fun i => Classical.choose_spec (hinv i)
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact ⟨[i],by simp [instructionWordValue]⟩
  | one => exact ⟨[],rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨w,rfl⟩ := ihx
    obtain ⟨v,rfl⟩ := ihy
    exact ⟨v++w,instructionWordValue_append G v w⟩
  | inv x hx ih =>
    obtain ⟨w,rfl⟩ := ih
    exact ⟨w.reverse.map inverseLabel,instructionWordValue_inverse G inverseLabel hi w⟩

theorem dense_instructionWords [TopologicalSpace H] (G : Fin m → H)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set H)) :
    DenseRange (instructionWordValue G) := by
  apply huniversal.mono
  intro x hx
  exact subgroup_instructionWord G hinv x hx

/-- A fixed finite approximation net is derived from inverse closure,
universality and compactness, rather than supplied as a calibration premise.
This is an existence theorem; no effective search complexity is claimed. -/
theorem finite_instructionNet [PseudoMetricSpace H] [CompactSpace H]
    (G : Fin m → H) (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set H))
    (ε : ℝ) (hε : 0<ε) :
    ∃ net : Finset (List (Fin m)),∀ U : H,∃ w∈net,dist U (instructionWordValue G w)<ε := by
  classical
  have hd := dense_instructionWords G hinv huniversal
  have hcover : (Set.univ : Set H)⊆⋃ w : List (Fin m),Metric.ball (instructionWordValue G w) ε := by
    intro U hU
    obtain ⟨w,hw⟩ := hd.exists_dist_lt U hε
    exact Set.mem_iUnion.mpr ⟨w,hw⟩
  obtain ⟨net,hnet⟩ := isCompact_univ.elim_finite_subcover
    (fun w : List (Fin m) => Metric.ball (instructionWordValue G w) ε)
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨net,fun U => ?_⟩
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp (hnet (Set.mem_univ U))
  obtain ⟨hwnet,hball⟩ := Set.mem_iUnion.mp hw
  exact ⟨w,hwnet,hball⟩

theorem uniform_instructionLength [PseudoMetricSpace H] [CompactSpace H]
    (G : Fin m → H) (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set H))
    (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℕ,∀ U : H,∃ w : List (Fin m),w.length≤L ∧ dist U (instructionWordValue G w)<ε := by
  obtain ⟨net,hnet⟩ := finite_instructionNet G hinv huniversal ε hε
  refine ⟨net.sup List.length,fun U => ?_⟩
  obtain ⟨w,hw,he⟩ := hnet U
  exact ⟨w,Finset.le_sup (f := List.length) hw,he⟩

end CircuitRecursion
