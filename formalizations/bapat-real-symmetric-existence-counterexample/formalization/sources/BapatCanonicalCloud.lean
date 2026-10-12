import BapatMaximizerBalance

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section

def complexifySphere4 (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4) (z : ComplexUnitSphere4) : ComplexUnitSphere4 :=
  ⟨complexifyRealIsometry R z, by simpa only [Metric.mem_sphere,dist_zero_right,
    complexifyRealIsometry_norm] using z.property⟩

theorem rotated_unitRows_product {n : ℕ} (v : Fin n → RealUnitSphere4)
    (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4) (z : ComplexUnitSphere4) :
    rowProductModulus (unitCoefficientRows (fun i => unitSphereHomeomorph R (v i))) z =
      rowProductModulus (unitCoefficientRows v) (complexifySphere4 R.symm z) := by
  rw [unitCoefficientRows_product_norm,unitCoefficientRows_product_norm]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg norm (realComplexLinear_isometry_symm R (v i) z)

theorem canonicalized_unitRows_product {n : ℕ} (v : Fin n → RealUnitSphere4)
    (z : ComplexUnitSphere4) (a : ℂ) (ha : ‖a‖=1)
    (R : RealSpace4 ≃ₗᵢ[ℝ] RealSpace4)
    (hR : complexifyRealIsometry R (a • (z:EuclideanSpace ℂ (Fin 4))) =
      canonicalComplex4 (balanceParameter z)) :
    ‖complexEval (formsProduct (unitCoefficientRows (fun i => unitSphereHomeomorph R (v i))))
      (canonicalComplex4 (balanceParameter z))‖ = rowProductModulus (unitCoefficientRows v) z := by
  rw [complexEval_formsProduct,norm_prod,unitCoefficientRows_product_norm]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonical_linear_modulus_transport z a ha R hR (v i)

/-- The genuine canonicalized triangular cloud: moving rotations, positive canonical
maxima, preserved uniform empirical law, and parameters tending to 1/2. -/
theorem exists_canonical_maximizing_cloud :
    ∃ (w : ℕ → ℕ → RealUnitSphere4) (t : ℕ → ℝ),
      (∀ n, 1/2 ≤ t n ∧ t n ≤ 1) ∧ Tendsto t atTop (𝓝 (1/2:ℝ)) ∧
      (∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop
        (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4)))) ∧
      (∀ n, 0 < ‖complexEval (formsProduct (cloudRows (w n) n)) (canonicalComplex4 (t n))‖) ∧
      (∀ n z, rowProductModulus (cloudRows (w n) n) z ≤
        ‖complexEval (formsProduct (cloudRows (w n) n)) (canonicalComplex4 (t n))‖) := by
  obtain ⟨u,z,hu,hp,hm,ht⟩ := exists_cloud_with_balanced_maximizers
  have hcoord (n : ℕ) := exists_canonical_coordinates (z n)
  choose a ha R hR using hcoord
  let w : ℕ → ℕ → RealUnitSphere4 := fun n i => unitSphereHomeomorph (R n) (u i)
  let t : ℕ → ℝ := fun n => balanceParameter (z n)
  have hvalue (n : ℕ) :
      ‖complexEval (formsProduct (cloudRows (w n) n)) (canonicalComplex4 (t n))‖ =
        rowProductModulus (cloudRows u n) (z n) :=
    canonicalized_unitRows_product (fun i : Fin n => u i.val) (z n) (a n) (ha n) (R n) (hR n)
  refine ⟨w,t,fun n => balanceParameter_mem (z n),ht,?_,?_,?_⟩
  · intro f
    let O : ℕ → Orthogonal4 := fun n => Unitary.linearIsometryEquiv.symm (R n)
    have h := moving_orthogonal_cloud u hu O f
    have he (n : ℕ) : Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm (R n)) = R n :=
      Unitary.linearIsometryEquiv.apply_symm_apply (R n)
    simpa only [empiricalAverage,w,O,orthogonalSphereAction,he] using h
  · intro n
    rw [hvalue]
    exact hp n
  · intro n z'
    rw [hvalue]
    change rowProductModulus (unitCoefficientRows (fun i : Fin n => unitSphereHomeomorph (R n) (u i.val))) z' ≤ _
    rw [rotated_unitRows_product]
    exact hm n _

end
end BapatRealExistence
