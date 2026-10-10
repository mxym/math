import GaussianSimplicialFlux
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Positive flux coefficients for every cell of an actual nondegenerate
simplicial Gaussian partition. Relabeling and affine independence supply the
normal basis at every vertex. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

lemma simplicial_normal_basis (v : Fin (d+2) → Space (d+1))
    (hv : AffineIndependent ℝ v) :
    ∃ B : Basis (Fin (d+1)) ℝ (Space (d+1)), ∀ i, B i = v 0 - v i.succ := by
  let e : Fin (d+1) ↪ {i : Fin (d+2) // i ≠ 0} :=
    ⟨fun i => ⟨i.succ, Fin.succ_ne_zero i⟩, fun i j h => Fin.succ_inj.mp (congrArg Subtype.val h)⟩
  have hi := ((affineIndependent_iff_linearIndependent_vsub ℝ v 0).mp hv).comp e e.injective
  have hn : LinearIndependent ℝ (fun i : Fin (d+1) => v 0 - v i.succ) := by
    have hh := hi.neg
    change LinearIndependent ℝ (fun i : Fin (d+1) => -(v i.succ - v 0)) at hh
    simpa only [neg_sub] using hh
  let B := basisOfLinearIndependentOfCardEqFinrank' _ hn (by simp [Space])
  exact ⟨B, fun i => by simp [B]⟩

/-- The coefficients here come from genuine Gaussian density integrals.
Symmetry is proved separately from the Gaussian rotational identity. -/
theorem gaussian_all_cells_positive_flux (v : Fin (d+2) → Space (d+1))
    (b : Fin (d+2) → ℝ) (hv : AffineIndependent ℝ v) :
    ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      (∀ i, w i i = 0) ∧ (∀ i j, i ≠ j → 0 < w i j) ∧
      ∀ i, rawWinningMoment v b i = ∑ j, w i j • (v i - v j) := by
  classical
  have hcell (i : Fin (d+2)) : ∃ f : Fin (d+1) → ℝ, (∀ j, 0 < f j) ∧
      rawWinningMoment v b i =
        ∑ j, f j • (v i - v (Equiv.swap 0 i j.succ)) := by
    let e : Equiv.Perm (Fin (d+2)) := Equiv.swap 0 i
    obtain ⟨B,hB⟩ := simplicial_normal_basis (v ∘ e) (hv.comp_embedding e.toEmbedding)
    obtain ⟨f,hp,hf⟩ := gaussian_simplicial_cell_positive_flux (v ∘ e) (b ∘ e) B hB
    refine ⟨f,hp,?_⟩
    rw [rawWinningMoment_reindex] at hf
    simpa [e] using hf
  choose f hp hf using hcell
  let w : Fin (d+2) → Fin (d+2) → ℝ := fun i j => Fin.cases 0 (f i) (Equiv.swap 0 i j)
  refine ⟨w, fun i => by simp [w], ?_, ?_⟩
  · intro i j hij
    have hj : Equiv.swap 0 i j ≠ 0 := by
      intro he
      have hh := congrArg (Equiv.swap 0 i) he
      exact hij (by simpa using hh.symm)
    rcases Fin.eq_zero_or_eq_succ (Equiv.swap 0 i j) with he | ⟨r,hr⟩
    · exact (hj he).elim
    · simpa [w,hr] using hp i r
  · intro i
    rw [hf i]
    symm
    calc
      (∑ j, w i j • (v i - v j)) =
          ∑ j, w i (Equiv.swap 0 i j) • (v i - v (Equiv.swap 0 i j)) :=
        (Equiv.sum_comp (Equiv.swap 0 i) _).symm
      _ = ∑ j : Fin (d+1), f i j • (v i - v (Equiv.swap 0 i j.succ)) := by
        simp [w,Fin.sum_univ_succ]

end GaussianMeasureBridge
