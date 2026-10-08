import GaussianPerimeterComparisonReduction
import GaussianMomentCovariance

/-!
An unconditional sharp-perimeter obstruction from the actual Gaussian radial
comparison. If any normalized covariance violates the regular-simplex
first-moment bound, some full simplicial, genuinely balanced Gaussian
winning cluster along its regular-covariance segment has strictly less
intrinsic perimeter than the regular model.

No Gaussian multi-bubble inequality, axiom, or unproved geometry is used.
The result is a reduction/obstruction, not a proof that the obstruction
cannot occur.
-/

open MeasureTheory ProbabilityTheory Module Matrix Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge
variable {d : ℕ}

/-- A violation of the sharp covariance comparison must produce a strictly
negative radial deficit at an interior covariance. -/
theorem exists_negative_covariance_radial_deficit
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (hbad : simplexConstant (d+2) < covarianceValue Q) :
    ∃ t : ℝ, t ∈ Ioo 0 1 ∧ covarianceRadialDeficit Q t < 0 := by
  classical
  by_contra hnot
  have hD (t : ℝ) (ht : t ∈ Ioo 0 1) :
      0 ≤ covarianceRadialDeficit Q t := by
    by_contra hneg
    exact hnot ⟨t, ht, lt_of_not_ge hneg⟩
  let H : ℝ → ℝ := fun t =>
    covarianceValue (covarianceSegment Q t)^2 - simplexConstant (d+2)^2
  obtain ⟨h0, hd0, hd, hi, hend⟩ := covariance_squared_radial_data Q hQ
  have hineq (t : ℝ) (ht : t ∈ Ioo 0 1) :
      t * deriv H t ≤ H t := by
    have he := hi t ht
    have hn := hD t ht
    linarith
  have hcomp := GaussianRadialComparison.radial_comparison
    H (deriv H) h0 hd0 hd hineq hend
  have hOne := hcomp 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hsq : covarianceValue Q ^ 2 - simplexConstant (d+2)^2 ≤ 0 := by
    simpa only [H, covarianceSegment_one] using hOne
  have hc : covarianceValue Q ≤ simplexConstant (d+2) := by
    have hn := simplexConstant_nonneg (k := d+2)
    nlinarith
  exact (not_lt.mpr hc) hbad

/-- Any counterexample to sharp covariance optimality produces an explicit
*actual balanced simplicial winning cluster* with a strictly sub-model
Gaussian intrinsic perimeter. In particular, the missing geometric
perimeter inequality is precisely an obstruction to such counterexamples. -/
theorem covariance_excess_forces_sharp_simplicial_perimeter_failure
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (hbad : simplexConstant (d+2) < covarianceValue Q) :
    ∃ t : ℝ, t ∈ Ioo 0 1 ∧
      ∃ v : Fin (d+2) → Space (d+1),
        AffineIndependent ℝ v ∧ scoreGram v = covarianceSegment Q t ∧
        ((∑ i, gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)^2 <
          (d+1:ℕ)*simplexConstant (d+2)^2/2 := by
  obtain ⟨t,ht,hneg⟩ := exists_negative_covariance_radial_deficit Q hQ hbad
  obtain ⟨r,w,hr,hg,hw,hp,hs,hf,hd,hi⟩ :=
    actual_covarianceSegment_radial_differential Q hQ t ht
  have hraw (i : Fin (d+2)) : rawWinningMoment r (canonicalPrices r) i =
      ∑ j, w i j • (r i-r j) := hf i
  have hnonneg (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i=j
    · subst j
      rw [hw i]
    · exact (hp i j hij).le
  have hval : covarianceValue (covarianceSegment Q t) =
      (∑ i, ∑ j, w i j*‖r i-r j‖^2)/2 := by
    rw [← hg, covarianceValue_scoreGram,
      ← balancedMoment_value r hr.injective]
    exact symmetric_flux_energy _ _ w hs hf
  have hcs := actual_flux_cauchy r w hnonneg
  rw [← hval] at hcs
  rw [covarianceRadialDeficit, actual_radial_trace Q t _ _ hd hi] at hneg
  have hn : 0 < ((d+1:ℕ):ℝ) := by positivity
  have hprod : covarianceValue (covarianceSegment Q t)*fluxTrace w <
      (d+1:ℕ)*simplexConstant (d+2)^2 := by
    have hh : covarianceValue (covarianceSegment Q t)*fluxTrace w/
        (d+1:ℕ) < simplexConstant (d+2)^2 := by linarith
    nlinarith [(div_lt_iff₀ hn).mp hh]
  have hflux : (fluxPerimeter r w)^2 <
      (d+1:ℕ)*simplexConstant (d+2)^2/2 := by
    nlinarith [hcs,hprod]
  refine ⟨t,ht,r,hr,hg,?_⟩
  rw [actual_simplicial_cluster_inner_perimeter r (canonicalPrices r) hr w hraw]
  exact hflux

#print axioms exists_negative_covariance_radial_deficit
#print axioms covariance_excess_forces_sharp_simplicial_perimeter_failure

end GaussianMeasureBridge


namespace GaussianMeasureBridge
variable {d e : ℕ}

/-- An actual equal-mass fractional-partition counterexample to the sharp
first-moment bound would force a genuine balanced simplicial Gaussian cluster
with strictly sub-regular intrinsic perimeter. This uses the already proved
primal-dual reduction, including zero/rank-deficient covariance handling. -/
theorem fractional_moment_excess_forces_sharp_simplicial_perimeter_failure
    (F : FractionalPartition e (d+2))
    (hmass : ∀ i, F.mass i = uniformMass (d+2) i)
    (hbad : simplexConstant (d+2)^2 < F.momentEnergy) :
    ∃ t : ℝ, t ∈ Ioo 0 1 ∧
      ∃ v : Fin (d+2) → Space (d+1),
        AffineIndependent ℝ v ∧ scoreGram v = covarianceSegment F.normalizedMomentCovariance t ∧
        ((∑ i, gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)^2 <
          (d+1:ℕ)*simplexConstant (d+2)^2/2 := by
  have hEpos : 0 < F.momentEnergy := by
    nlinarith [sq_nonneg (simplexConstant (d+2))]
  have hQ : NormalizedCovariance F.normalizedMomentCovariance :=
    F.normalizedMomentCovariance_mem hEpos
  have hCbad : simplexConstant (d+2) <
      covarianceValue F.normalizedMomentCovariance := by
    by_contra hnot
    have hCle : covarianceValue F.normalizedMomentCovariance ≤ simplexConstant (d+2) :=
      le_of_not_gt hnot
    have hscore : equalMassValue F.moment ≤
        simplexConstant (d+2)*Real.sqrt F.momentEnergy := by
      rw [F.equalMassValue_moment_normalize hEpos]
      calc
        Real.sqrt F.momentEnergy * covarianceValue F.normalizedMomentCovariance ≤
          Real.sqrt F.momentEnergy * simplexConstant (d+2) :=
            mul_le_mul_of_nonneg_left hCle (Real.sqrt_nonneg F.momentEnergy)
        _ = _ := mul_comm _ _
    have hbound := F.momentEnergy_le_sq_of_score_bound hmass
      (simplexConstant (d+2)) (simplexConstant_nonneg) hscore
    exact (not_lt.mpr hbound) hbad
  exact covariance_excess_forces_sharp_simplicial_perimeter_failure
    F.normalizedMomentCovariance hQ hCbad

#print axioms fractional_moment_excess_forces_sharp_simplicial_perimeter_failure

end GaussianMeasureBridge


namespace GaussianMeasureBridge
variable {d : ℕ}

/-- Exact decomposition of the *actual* Gaussian covariance radial deficit
into the weighted pair-edge Cauchy slack and the difference from the
regular simplex squared perimeter. The first summand is nonnegative
unconditionally, without invoking Gaussian multi-bubble geometry. -/
theorem actual_radial_deficit_perimeter_variance_split
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : NormalizedCovariance Q) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    ∃ v : Fin (d+2) → Space (d+1),
      ∃ w : Fin (d+2) → Fin (d+2) → ℝ,
      AffineIndependent ℝ v ∧ scoreGram v = covarianceSegment Q t ∧
      (∀ i j, 0 ≤ w i j) ∧
      covarianceRadialDeficit Q t =
        (2 / (d+1:ℕ)) *
          ((fluxTrace w * covarianceValue (covarianceSegment Q t) / 2 -
              (fluxPerimeter v w)^2) +
            ((fluxPerimeter v w)^2 -
              (d+1:ℕ)*simplexConstant (d+2)^2/2)) ∧
      0 ≤ fluxTrace w*covarianceValue (covarianceSegment Q t)/2 -
        (fluxPerimeter v w)^2 := by
  obtain ⟨v,w,hv,hg,hw,hp,hs,hf,hd,hi⟩ :=
    actual_covarianceSegment_radial_differential Q hQ t ht
  have hnonneg (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i=j
    · subst j; rw [hw i]
    · exact (hp i j hij).le
  have hval : covarianceValue (covarianceSegment Q t) =
      (∑ i,∑ j,w i j*‖v i-v j‖^2)/2 := by
    rw [← hg,covarianceValue_scoreGram,← balancedMoment_value v hv.injective]
    exact symmetric_flux_energy _ _ w hs hf
  have hcs := actual_flux_cauchy v w hnonneg
  rw [← hval] at hcs
  refine ⟨v,w,hv,hg,hnonneg,?_,?_⟩
  · rw [covarianceRadialDeficit,actual_radial_trace Q t _ _ hd hi]
    have hn : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · nlinarith [hcs]

#print axioms actual_radial_deficit_perimeter_variance_split
end GaussianMeasureBridge


namespace GaussianMeasureBridge

/-!
An exact finite weighted Cauchy-defect identity. It does not require
nonnegative weights; positivity is needed only when interpreting the
result as a variance in the actual Gaussian facet application.
-/

/-- Exact weighted edge-variance identity around the weighted mean.
This quantifies, rather than merely bounds, the weighted Cauchy defect. -/
theorem finite_weighted_cauchy_defect_eq_variance
    {ι : Type*} [Fintype ι] (w ell : ι → ℝ)
    (hA : (∑ i, w i) ≠ 0) :
    (∑ i, w i) * (∑ i, w i * ell i ^ 2) -
        (∑ i, w i * ell i) ^ 2 =
      (∑ i, w i) *
        (∑ i, w i *
          (ell i - (∑ j, w j * ell j) / (∑ j, w j)) ^ 2) := by
  classical
  let A : ℝ := ∑ i, w i
  let B : ℝ := ∑ i, w i * ell i
  let C : ℝ := ∑ i, w i * ell i ^ 2
  let m : ℝ := B / A
  have hA' : A ≠ 0 := hA
  have hm : A * m = B := by
    dsimp only [m]
    field_simp
  have hexpand :
      (∑ i, w i * (ell i - m)^2) = C - 2*m*B + m^2*A := by
    calc
      _ = ∑ i, (w i*ell i^2 - (2*m)*(w i*ell i) + m^2*w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C - 2*m*B + m^2*A := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
  change A*C - B^2 = A*(∑ i, w i*(ell i-m)^2)
  rw [hexpand]
  calc
    A*C-B^2 = A*C-2*(A*m)*B+(A*m)^2 := by rw [hm]; ring
    _ = A*(C-2*m*B+m^2*A) := by ring

#print axioms finite_weighted_cauchy_defect_eq_variance

end GaussianMeasureBridge
