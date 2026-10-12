import Entry005.ZonotopeFormula
import Entry005.FiniteDeterminantTupleInjection

/-! The finite-law zonotope identity connects actual discrete iid first
absolute determinant moments to actual symmetric segment-sum volumes.
No assertion that the input atoms or weights come from body facets is made. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem finite_zonotope_reindex {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : ι → E) (e : κ ≃ ι) : finiteZonotope (fun j => g (e j)) = finiteZonotope g := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t (e.symm i), fun i => ht (e.symm i), ?_⟩
    simpa using (e.sum_comp (fun i => t (e.symm i) • g i)).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun j => t (e j), fun j => ht (e j), ?_⟩
    exact e.sum_comp (fun i => t i • g i)

theorem finite_zonotope_volume_matrix_fintype {ι : Type*} [Fintype ι] {d : ℕ}
    (g : ι → EuclideanSpace ℝ (Fin d)) :
    (volume (finiteZonotope g)).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        ∑ σ : Fin d ↪ ι, |Matrix.det (fun i j => g (σ j) i)| := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← finite_zonotope_reindex g e, finite_zonotope_volume_matrix]
  congr 1
  apply Fintype.sum_equiv (Equiv.embeddingCongr (Equiv.refl (Fin d)) e)
  intro σ
  rfl

theorem finite_zonotope_volume_horizontal_tuple_sum {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) :
    (volume (finiteZonotope (fun i => WithLp.toLp 2 (v i)))).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        ∑ b : Fin d → ι, |horizontalDeterminant (fun j => v (b j))| := by
  rw [finite_zonotope_volume_matrix_fintype]
  congr 1
  exact (fintype_determinant_tuple_sum_eq_injection_sum v).symm

/-- The actual finite symmetric-segment sum of probability weights times atoms. -/
def finiteLawZonotope {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  finiteZonotope (fun i => p i • WithLp.toLp 2 (x i))

theorem finite_weighted_horizontal_determinant {ι : Type*} {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (b : Fin d → ι) :
    |horizontalDeterminant (fun j l => p (b j) * x (b j) l)| =
      (∏ j, p (b j)) * |horizontalDeterminant (fun j => x (b j))| := by
  have hdet : horizontalDeterminant (fun j l => p (b j) * x (b j) l) =
      (∏ j, p (b j)) * horizontalDeterminant (fun j => x (b j)) := by
    simpa only [horizontalDeterminant, Matrix.of_apply] using
      Matrix.det_mul_row (fun j => p (b j)) (Matrix.of (fun i j => x (b j) i))
  rw [hdet, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun j _ => hp (b j)))]

theorem finite_law_zonotope_volume_weighted_tuple_sum {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (volume (finiteLawZonotope p x)).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        ∑ b : Fin d → ι, (∏ j, p (b j)) * |horizontalDeterminant (fun j => x (b j))| := by
  have hg : (fun i => p i • WithLp.toLp 2 (x i)) =
      (fun i => WithLp.toLp 2 (fun l => p i * x i l)) := by
    funext i
    ext l
    rfl
  unfold finiteLawZonotope
  rw [hg, finite_zonotope_volume_horizontal_tuple_sum]
  simp_rw [finite_weighted_horizontal_determinant p x hp]

/-- Finite cone data give the exact volume/first-moment identity for the
zonotope with generators `(aᵢ hᵢ/M) • (nᵢ/hᵢ)`. No facet premise is needed. -/
theorem finite_cone_zonotope_volume_first_moment {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {d : ℕ}
    (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hmass : ∑ i, a i * h i = M) :
    (volume (finiteLawZonotope (fun i => a i * h i / M) (finiteConePoint n h))).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        (∫ base, |horizontalDeterminant base| ∂iidLaw (finiteConeLaw a h n M) d) := by
  rw [finite_law_zonotope_volume_weighted_tuple_sum _ _
    (fun i => div_nonneg (mul_nonneg (ha i) (hh i).le) hM.le)]
  rw [finite_cone_horizontal_determinant_expectation a h n M ha hh hM hmass,
    Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact finite_cone_weighted_sample_determinant a h n M ha hh b

/-- The discrete measure determined by the actual finite atom weights. -/
def finiteAtomLaw {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.sum (fun i => ENNReal.ofReal (p i) • Measure.dirac (x i))

theorem finite_cone_point_height_one {ι : Type*} {d : ℕ} (x : ι → Fin d → ℝ) :
    finiteConePoint x (fun _ => 1) = x := by
  funext i j
  simp [finiteConePoint]

theorem finite_atom_law_eq_cone {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) :
    finiteAtomLaw p x = finiteConeLaw p (fun _ => 1) x 1 := by
  simp [finiteAtomLaw, finiteConeLaw, finite_cone_point_height_one]

theorem finite_atom_probability {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteAtomLaw p x) := by
  rw [finite_atom_law_eq_cone]
  exact finite_cone_probability p (fun _ => 1) x 1 hp (fun _ => zero_lt_one) zero_lt_one
    (by simpa using hsum)

/-- Every positive-weight atom is in the actual discrete measure support.
Zero-weight indices are allowed in the volume theorem and give zero generators. -/
theorem finite_atom_mem_support_of_pos {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (i : ι) (hi : 0 < p i) :
    x i ∈ (finiteAtomLaw p x).support := by
  apply (Measure.mem_support_iff_forall (x i)).2
  intro U hU
  have hx : x i ∈ U := mem_of_mem_nhds hU
  have hle := (ENNReal.le_tsum i).trans
    (Measure.le_sum_apply (fun j => ENNReal.ofReal (p j) • Measure.dirac (x j)) U)
  have hpos : 0 < (ENNReal.ofReal (p i) • Measure.dirac (x i)) U := by
    simpa only [Measure.smul_apply, Measure.dirac_apply_of_mem hx, smul_eq_mul, mul_one] using
      (ENNReal.ofReal_pos.mpr hi)
  exact hpos.trans_le hle

/-- Exact finite-probability zonotope identity: the moment uses the actual iid
law and the first absolute determinant, and includes all tuples. -/
theorem finite_atom_zonotope_volume_first_moment {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (volume (finiteLawZonotope p x)).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        (∫ base, |horizontalDeterminant base| ∂iidLaw (finiteAtomLaw p x) d) := by
  rw [finite_atom_law_eq_cone]
  simpa only [mul_one, div_one, finite_cone_point_height_one] using
    finite_cone_zonotope_volume_first_moment p (fun _ => 1) x 1 hp
      (fun _ => zero_lt_one) zero_lt_one (by simpa using hsum)

/-- The lifted segment sum uses atoms `(1,xᵢ)` in the literal height-first
coordinate order used by `witnessMatrix`. -/
def finiteLiftedLawZonotope {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  finiteLawZonotope p (fun i => Fin.cases 1 (x i))

theorem finite_cone_lifted_zonotope_volume_first_moment {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {d : ℕ}
    (a h : ι → ℝ) (n : ι → Fin d → ℝ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 < h i) (hM : 0 < M)
    (hmass : ∑ i, a i * h i = M) :
    (volume (finiteLiftedLawZonotope (fun i => a i * h i / M)
      (finiteConePoint n h))).toReal =
      (2 ^ (d + 1) / ((d + 1).factorial : ℝ)) *
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)|
          ∂iidLaw (finiteConeLaw a h n M) (d + 1)) := by
  have hpoint : (fun i => Fin.cases 1 (finiteConePoint n h i)) =
      finiteConePoint (finiteFacetLift h n) h := by
    funext i j
    induction j using Fin.cases with
    | zero => simp [finiteConePoint, finiteFacetLift, (hh i).ne']
    | succ j => simp [finiteConePoint, finiteFacetLift]
  unfold finiteLiftedLawZonotope
  rw [hpoint, finite_law_zonotope_volume_weighted_tuple_sum _ _
    (fun i => div_nonneg (mul_nonneg (ha i) (hh i).le) hM.le)]
  rw [finite_cone_lifted_determinant_expectation a h n M ha hh hM hmass,
    Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact finite_cone_weighted_sample_determinant a h (finiteFacetLift h n) M ha hh b

theorem finite_atom_lifted_zonotope_volume_first_moment {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {d : ℕ}
    (p : ι → ℝ) (x : ι → Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (volume (finiteLiftedLawZonotope p x)).toReal =
      (2 ^ (d + 1) / ((d + 1).factorial : ℝ)) *
        (∫ w : Fin (d + 1) → Fin d → ℝ,
          |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteAtomLaw p x) (d + 1)) := by
  rw [finite_atom_law_eq_cone]
  simpa only [mul_one, div_one, finite_cone_point_height_one] using
    finite_cone_lifted_zonotope_volume_first_moment p (fun _ => 1) x 1 hp
      (fun _ => zero_lt_one) zero_lt_one (by simpa using hsum)

end Entry005
