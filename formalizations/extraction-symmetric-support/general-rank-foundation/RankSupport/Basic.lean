import SymmetricSupport.PureSpan
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

open scoped BigOperators
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport

/-- Actual tensor coordinates of possibly different one-copy vectors. -/
def productVector (D k : ℕ) (z : Fin k → Fin D → ℂ) : Word D k → ℂ :=
  fun w => ∏ i, z i (w i)

/-- The intrinsic rank-budget space, constructed from actual vectors. Its
identification with the sum of Schur blocks is not built into the definition. -/
def rankBudgetSpace (D k s : ℕ) : Submodule ℂ (Word D k → ℂ) :=
  Submodule.span ℂ {v | ∃ z : Fin k → Fin D → ℂ,
    Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ s ∧ v = productVector D k z}

theorem productVector_mem_rankBudgetSpace (D k s : ℕ)
    (z : Fin k → Fin D → ℂ)
    (hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ s) :
    productVector D k z ∈ rankBudgetSpace D k s :=
  Submodule.subset_span ⟨z, hz, rfl⟩

theorem rankBudgetSpace_mono (D k : ℕ) {s t : ℕ} (hst : s ≤ t) :
    rankBudgetSpace D k s ≤ rankBudgetSpace D k t := by
  apply Submodule.span_mono
  rintro v ⟨z, hz, rfl⟩
  exact ⟨z, hz.trans hst, rfl⟩

theorem constant_factors_span_finrank_le_one (D k : ℕ) (z : Fin D → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun _ : Fin k => z))) ≤ 1 := by
  have hle : Submodule.span ℂ (Set.range (fun _ : Fin k => z)) ≤ Submodule.span ℂ {z} := by
    apply Submodule.span_mono
    rintro v ⟨i, rfl⟩
    exact Set.mem_singleton z
  exact (Submodule.finrank_mono hle).trans (by simpa using finrank_span_le_card ({z} : Set (Fin D → ℂ)))

theorem purePower_mem_rankBudgetSpace (D k s : ℕ) (hs : 1 ≤ s) (z : Fin D → ℂ) :
    purePower D k z ∈ rankBudgetSpace D k s :=
  productVector_mem_rankBudgetSpace D k s (fun _ => z)
    ((constant_factors_span_finrank_le_one D k z).trans hs)

theorem symmetric_range_le_rankBudgetSpace (D k s : ℕ) (hs : 1 ≤ s) :
    LinearMap.range (symmetricProjector D k).mulVecLin ≤ rankBudgetSpace D k s := by
  rw [symmetricProjector_range_eq_purePower_span]
  apply Submodule.span_le.mpr
  rintro v ⟨z, rfl⟩
  exact purePower_mem_rankBudgetSpace D k s hs z

theorem productVector_factors_smul (D k : ℕ) (c : Fin k → ℂ) (u : Fin D → ℂ) :
    productVector D k (fun i => c i • u) = (∏ i, c i) • purePower D k u := by
  ext w
  simp [productVector, purePower, Finset.prod_mul_distrib]

theorem rank_one_productVector_mem_symmetric_range (D k : ℕ)
    (z : Fin k → Fin D → ℂ)
    (hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ 1) :
    productVector D k z ∈ LinearMap.range (symmetricProjector D k).mulVecLin := by
  classical
  let S := Submodule.span ℂ (Set.range z)
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := ℂ) (V := S)).mp hz
  have hzi (i : Fin k) : z i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hc : ∀ i : Fin k, ∃ c : ℂ, c • (u : Fin D → ℂ) = z i := by
    intro i
    obtain ⟨c, hc⟩ := hu ⟨z i, hzi i⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hc
  have heq : z = fun i => c i • (u : Fin D → ℂ) := by
    funext i
    exact (hc i).symm
  rw [heq, productVector_factors_smul]
  apply Submodule.smul_mem
  exact ⟨purePower D k (u : Fin D → ℂ), symmetricProjector_fixes_purePower D k _⟩

/-- The intrinsic general-rank construction agrees with the explicitly counted
symmetric support at rank budget one. -/
theorem rankBudgetSpace_one_eq_symmetric_range (D k : ℕ) :
    rankBudgetSpace D k 1 = LinearMap.range (symmetricProjector D k).mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩
    exact rank_one_productVector_mem_symmetric_range D k z hz
  · exact symmetric_range_le_rankBudgetSpace D k 1 le_rfl

end ExtractionRankSupport
