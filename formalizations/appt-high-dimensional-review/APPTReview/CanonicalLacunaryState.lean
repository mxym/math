import APPTReview.LacunaryDensity
import APPTReview.ProjectionState
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def cappedRankSupport (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) : Finset ι :=
  Classical.choose (Finset.exists_subset_card_eq
    (show min r (Fintype.card ι)≤(Finset.univ : Finset ι).card by simpa using Nat.min_le_right r (Fintype.card ι)))

theorem cappedRankSupport_card (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) :
    (cappedRankSupport ι r).card=min r (Fintype.card ι) :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (show min r (Fintype.card ι)≤(Finset.univ : Finset ι).card by simpa using Nat.min_le_right r (Fintype.card ι)))).2

/-- Integer ranks are obtained by a natural floor and capped only to make the
matrix total in all dimensions. The APPT proof retains their actual traces. -/
noncomputable def canonicalScaleProjection (m n : ℕ) (d : ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  setProjection (cappedRankSupport (Fin m × Fin n) ⌊(m:ℝ)^(2-d)⌋₊)

theorem canonicalScaleProjection_properties (m n : ℕ) (d : ℝ) :
    (canonicalScaleProjection m n d).PosSemidef ∧
    (1-canonicalScaleProjection m n d).PosSemidef ∧
    canonicalScaleProjection m n d*canonicalScaleProjection m n d=canonicalScaleProjection m n d ∧
    (canonicalScaleProjection m n d).trace.re≤(m:ℝ)^(2-d) := by
  let S := cappedRankSupport (Fin m × Fin n) ⌊(m:ℝ)^(2-d)⌋₊
  have hP : (setProjection S).IsHermitian := setProjection_hermitian S
  have hsq := setProjection_sq S
  refine ⟨hermitian_idempotent_posSemidef _ hP hsq,
    hermitian_idempotent_complement_posSemidef _ hP hsq,hsq,?_⟩
  rw [canonicalScaleProjection,setProjection_trace,cappedRankSupport_card]
  simp only [Complex.natCast_re]
  have hfloor : (⌊(m:ℝ)^(2-d)⌋₊:ℝ)≤(m:ℝ)^(2-d) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hmin : (min ⌊(m:ℝ)^(2-d)⌋₊ (Fintype.card (Fin m × Fin n)):ℝ)≤⌊(m:ℝ)^(2-d)⌋₊ :=
    by exact_mod_cast Nat.min_le_left ⌊(m:ℝ)^(2-d)⌋₊ (Fintype.card (Fin m × Fin n))
  simpa only [Nat.cast_min] using hmin.trans hfloor

noncomputable def coordinateUnitVector (m n : ℕ) (hm : 0<m) (hn : 0<n) : Fin m × Fin n → ℂ :=
  Pi.single (⟨0,hm⟩,⟨0,hn⟩) (1:ℂ)

theorem coordinateUnitVector_norm (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    star (coordinateUnitVector m n hm hn) ⬝ᵥ coordinateUnitVector m n hm hn=1 := by
  simp [coordinateUnitVector,dotProduct,Pi.single_apply]

noncomputable def canonicalLacunaryState (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (m n : ℕ) (hm : 0<m) (hn : 0<n) :=
  lacunaryDensity m n ds e a (canonicalScaleProjection m n) (coordinateUnitVector m n hm hn)

/-- Actual integer-projection density matrices, with no projection/frame/rank
witness left for the caller to construct. A common threshold covers every n>=m. -/
theorem canonical_lacunary_states_appt (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B a : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ha : 0≤a) (ha2 : a<2) (henergy : scaleEnergyBound ds e B<2) :
    ∃ M : ℕ, 2≤M ∧ ∀ (m n : ℕ) (hm0 : 0<m) (hn0 : 0<n), M≤m → m≤n →
      APPT.Quantum.IsDensity (canonicalLacunaryState ds e a m n hm0 hn0) ∧
      APPT.Quantum.AbsolutelyPPT (canonicalLacunaryState ds e a m n hm0 hn0) := by
  obtain ⟨M,hM2,hM⟩ := lacunary_density_eventually ds hds hd1 e B a hB he heB ha ha2 henergy
  refine ⟨M,hM2,?_⟩
  intro m n hm0 hn0 hm hmn
  exact hM m n hm hmn (canonicalScaleProjection m n)
    (fun d _ => (canonicalScaleProjection_properties m n d).1)
    (fun d _ => (canonicalScaleProjection_properties m n d).2.1)
    (fun d _ => (canonicalScaleProjection_properties m n d).2.2.2)
    (coordinateUnitVector m n hm0 hn0) (coordinateUnitVector_norm m n hm0 hn0)

end APPTReview
