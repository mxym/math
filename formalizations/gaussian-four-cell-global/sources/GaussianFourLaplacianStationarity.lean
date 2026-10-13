import GaussianInteriorFluxStationarity
import GaussianRegularValue
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Finite-dimensional consequence of the interior stationarity equations for four
labels.  If a symmetric positive facet Laplacian is orthogonal (in the trace
pairing) to every centered trace-zero Hermitian direction, it is a scalar
multiple of the regular centered projection.  Equivalently, all six facet
weights are equal.

This is only a stationarity lemma; it is not a global-maximizer or perimeter
theorem.
-/

open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge

lemma four_laplacian_scalar_of_stationary
    (w : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, w i i = 0)
    (hs : ∀ i j, w i j = w j i)
    (hstat : ∀ D : Matrix (Fin 4) (Fin 4) ℝ,
      D.IsHermitian → (∀ i, (∑ j, D i j) = 0) → D.trace = 0 →
      (facetLaplacian w * D).trace = 0) :
    ∀ i j, i ≠ j → w i j = w 0 1 := by
  let L : Matrix (Fin 4) (Fin 4) ℝ := facetLaplacian w
  let R : Matrix (Fin 4) (Fin 4) ℝ := regularCovariance 4
  let t : ℝ := L.trace
  let A : Matrix (Fin 4) (Fin 4) ℝ := L - t • R
  have hL : L.IsHermitian := facetLaplacian_symmetric w hs
  have hR : R.IsHermitian := (regularCovariance_normalized (k := 4) (by norm_num)).1.isHermitian
  have hA : A.IsHermitian := by
    dsimp [A]
    exact hL.sub (hR.smul (by simp [IsSelfAdjoint]))
  have hLrow (i : Fin 4) : ∑ j, L i j = 0 := facetLaplacian_row_sum w i
  have hRrow (i : Fin 4) : ∑ j, R i j = 0 :=
    (regularCovariance_normalized (k := 4) (by norm_num)).2.1 i
  have hArow (i : Fin 4) : ∑ j, A i j = 0 := by
    simp only [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hLrow, hRrow, mul_zero,
      sub_zero]
  have hAtrace : A.trace = 0 := by
    dsimp [A, t]
    rw [Matrix.trace_sub, Matrix.trace_smul]
    simp only [R]
    rw [(regularCovariance_normalized (k := 4) (by norm_num)).2.2]
    ring
  have hRAtrace : (R * A).trace = 0 := by
    have hAsym (i j : Fin 4) : A i j = A j i := by
      simpa using hA.apply j i
    have hAcol (j : Fin 4) : ∑ i, A i j = 0 := by
      calc
        ∑ i, A i j = ∑ i, A j i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hAsym i j
        _ = 0 := hArow j
    have hdiag (i : Fin 4) : (regularCovariance 4 * A) i i =
        (1 / 3 : ℝ) * A i i := by
      simp only [Matrix.mul_apply, regularCovariance_apply]
      fin_cases i <;> simp [Fin.sum_univ_succ] at hAcol ⊢ <;>
        linarith [hAcol 0, hAcol 1, hAcol 2, hAcol 3]
    calc
      (R * A).trace = (regularCovariance 4 * A).trace := by rfl
      _ = ∑ i, (regularCovariance 4 * A) i i := by rfl
      _ = ∑ i, (1 / 3 : ℝ) * A i i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hdiag i
      _ = (1 / 3 : ℝ) * A.trace := by
        change (∑ i, (1 / 3 : ℝ) * A i i) =
          (1 / 3 : ℝ) * (∑ i, A i i)
        rw [← Finset.mul_sum]
      _ = 0 := by rw [hAtrace]; ring
  have hLA : (L * A).trace = 0 := by
    exact hstat A hA hArow hAtrace
  have hAA : (A * A).trace = 0 := by
    have hAdef : A = L - t • R := by rfl
    calc
      (A * A).trace = ((L - t • R) * A).trace := by rw [hAdef]
      _ = (L * A).trace - (t • (R * A)).trace := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul]
      _ = 0 := by rw [Matrix.trace_smul, hLA, hRAtrace]; ring
  have hAzero : A = 0 := by
    have hAA' : (Aᴴ * A).trace = 0 := by
      rw [hA]
      exact hAA
    exact (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp hAA'
  intro i j hij
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hAzero
  have hLentry : L i j = -w i j := by
    simp [L, facetLaplacian, hij]
  have hRentry : R i j = -(1 / 12 : ℝ) := by
    simp [R, regularCovariance_apply, hij]
    norm_num
  have htentry : t * R i j = t * (-(1 / 12 : ℝ)) := by rw [hRentry]
  have hentry' : L i j - t * R i j = 0 := by
    simpa [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hentry
  rw [hLentry, hRentry] at hentry'
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h0entry : L 0 1 = -w 0 1 := by
    simp [L, facetLaplacian, h01]
  have hbase0 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hAzero
  have hbase : L 0 1 - t * R 0 1 = 0 := by
    simpa [A, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hbase0
  have hR01 : R 0 1 = -(1 / 12 : ℝ) := by
    simp [R, regularCovariance_apply, h01]
    norm_num
  rw [h0entry, hR01] at hbase
  nlinarith

theorem centered_local_max_equal_flux_weights
    (Q : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : Q.IsHermitian)
    (hzQ : ∀ i, (∑ j, Q i j) = 0)
    (hprincipal : (principalCovariance Q).PosDef)
    (hmax : CenteredDirectionalLocalMax 2 Q) :
    ∃ w : Fin 4 → Fin 4 → ℝ,
      (∀ i, w i i = 0) ∧
      (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i j, i ≠ j → w i j = w 0 1) := by
  obtain ⟨w, hd, hp, hs, hstat⟩ :=
    centered_local_max_flux_stationary Q hQ hzQ hprincipal hmax
  refine ⟨w, hd, hp, hs, ?_⟩
  exact four_laplacian_scalar_of_stationary w hd hs hstat

theorem centered_local_max_affine_moment_relation
    (Q : Matrix (Fin 4) (Fin 4) ℝ)
    (hQ : Q.IsHermitian)
    (hzQ : ∀ i, (∑ j, Q i j) = 0)
    (hprincipal : (principalCovariance Q).PosDef)
    (hmax : CenteredDirectionalLocalMax 2 Q) :
    ∃ r : Fin 4 → Space 3, ∃ w : Fin 4 → Fin 4 → ℝ, ∃ c : ℝ,
      AffineIndependent ℝ r ∧ scoreGram r = Q ∧
      (∀ i, w i i = 0) ∧
      (∀ i j, i ≠ j → 0 < w i j) ∧
      (∀ i j, w i j = w j i) ∧
      (∀ i, balancedMoment r i =
        (4 * c) • r i - c • (∑ j, r j)) ∧
      c = w 0 1 := by
  obtain ⟨r,w,hr,hg,hd,hp,hs,hm,hder⟩ :=
    centered_covariance_fixed_flux_differential Q hQ hzQ hprincipal
  have hstat : ∀ D : Matrix (Fin 4) (Fin 4) ℝ,
      D.IsHermitian → (∀ i, (∑ j, D i j) = 0) → D.trace = 0 →
      (facetLaplacian w * D).trace = 0 := by
    intro D hD hzD htD
    have hloc := hmax D hD hzD htD
    have hzero : deriv (fun t : ℝ => covarianceValue (Q+t•D)) 0 = 0 :=
      hloc.deriv_eq_zero
    have hd' := hder D hD hzD
    rw [hd'.deriv] at hzero
    linarith
  have heq : ∀ i j, i ≠ j → w i j = w 0 1 :=
    four_laplacian_scalar_of_stationary w hd hs hstat
  let c : ℝ := w 0 1
  refine ⟨r,w,c,hr,hg,hd,hp,hs,?_,rfl⟩
  intro i
  calc
    balancedMoment r i = ∑ j, w i j • (r i-r j) := hm i
    _ = ∑ j, c • (r i-r j) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp [hd]
      · rw [heq i j hij]
    _ = c • (∑ j, (r i-r j)) := by
      rw [Finset.smul_sum]
    _ = (4 * c) • r i - c • (∑ j, r j) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      module

end GaussianMeasureBridge
