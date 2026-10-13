import HydrologyTree.DiagonalGauge
import HydrologyTree.LinearForcedODE

/-! Actual state/trajectory equivalence under a diagonal gauge normalized at the
fixed input-observation vertex. The input is UNCHANGED, not silently rescaled. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

def normalizedGaugeState (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun z v := h v/h o*z v
  invFun z v := h o/h v*z v
  left_inv z := by funext v; dsimp; field_simp [hh v,hh o]
  right_inv z := by funext v; dsimp; field_simp [hh v,hh o]
  map_add' z q := by funext v; dsimp; ring
  map_smul' c z := by funext v; dsimp; ring

@[simp] lemma normalizedGaugeState_apply (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (z : V → ℝ) (v : V) : normalizedGaugeState h hh o z v=h v/h o*z v := rfl

@[simp] lemma normalizedGaugeState_root (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V) (z : V → ℝ) :
    normalizedGaugeState h hh o z o=z o := by simp [normalizedGaugeState_apply,hh o]

@[simp] lemma normalizedGaugeState_symm_root (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V) (z : V → ℝ) :
    (normalizedGaugeState h hh o).symm z o=z o := by
  change h o/h o*z o=z o
  simp [hh o]

def normalizedGaugeTrajectory (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V) :
    (ℝ → V → ℝ) ≃ (ℝ → V → ℝ) where
  toFun z s := normalizedGaugeState h hh o (z s)
  invFun z s := (normalizedGaugeState h hh o).symm (z s)
  left_inv z := by funext s; exact (normalizedGaugeState h hh o).symm_apply_apply (z s)
  right_inv z := by funext s; exact (normalizedGaugeState h hh o).apply_symm_apply (z s)

@[simp] lemma normalizedGaugeTrajectory_root (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (z : ℝ → V → ℝ) (s : ℝ) : normalizedGaugeTrajectory h hh o z s o=z s o :=
  normalizedGaugeState_root h hh o (z s)

@[simp] lemma normalizedGaugeTrajectory_symm_root (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (z : ℝ → V → ℝ) (s : ℝ) : (normalizedGaugeTrajectory h hh o).symm z s o=z s o :=
  normalizedGaugeState_symm_root h hh o (z s)

lemma normalizedGaugeState_mulVec (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (z : V → ℝ) :
    normalizedGaugeState h hh o (A*ᵥz)=diagonalGauge h A*ᵥnormalizedGaugeState h hh o z := by
  funext i
  simp only [normalizedGaugeState_apply,Matrix.mulVec,dotProduct,diagonalGauge_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hh j,hh o]
  <;> ring

lemma normalizedGaugeState_input (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V) :
    normalizedGaugeState h hh o (Pi.single o 1)=Pi.single o 1 := by
  funext i
  by_cases hi : i=o
  · subst i
    simp [hh o]
  · simp [Pi.single_apply,hi,Ne.symm hi]

lemma normalizedGaugeState_field (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (z : V → ℝ) (a : ℝ) :
    normalizedGaugeState h hh o (A*ᵥz+a • (Pi.single o 1 : V → ℝ))=
      diagonalGauge h A*ᵥnormalizedGaugeState h hh o z+a • (Pi.single o 1 : V → ℝ) := by
  rw [map_add,map_smul,normalizedGaugeState_mulVec,normalizedGaugeState_input]

/-- The transported actual ODE has identical forcing and identical root output. -/
theorem normalizedGauge_solution_forward (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (u : ℝ → ℝ) (z : ℝ → V → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single o 1) u z) :
    IsForcedMatrixSolution (diagonalGauge h A) (Pi.single o 1) u (normalizedGaugeTrajectory h hh o z) := by
  intro s
  have he := (normalizedGaugeState h hh o).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hz s)
  apply he.congr_deriv
  exact normalizedGaugeState_field h hh o A (z s) (u s)

/-- Both directions hold for every actual classical trajectory; no continuity
of the forcing beyond what the trajectory definition requires is imposed. -/
theorem normalizedGauge_solution_iff (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (u : ℝ → ℝ) (z : ℝ → V → ℝ) :
    IsForcedMatrixSolution A (Pi.single o 1) u z ↔
      IsForcedMatrixSolution (diagonalGauge h A) (Pi.single o 1) u (normalizedGaugeTrajectory h hh o z) := by
  constructor
  · exact normalizedGauge_solution_forward h hh o A u z
  · intro hz s
    have he := (normalizedGaugeState h hh o).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hz s)
    change HasDerivAt (fun t => (normalizedGaugeState h hh o).symm
      (normalizedGaugeState h hh o (z t)))
      ((normalizedGaugeState h hh o).symm (diagonalGauge h A*ᵥnormalizedGaugeState h hh o (z s)+
        u s • (Pi.single o 1 : V → ℝ))) s at he
    simp only [LinearEquiv.symm_apply_apply] at he
    apply he.congr_deriv
    have hfield := normalizedGaugeState_field h hh o A (z s) (u s)
    exact (congrArg (normalizedGaugeState h hh o).symm hfield).symm.trans
      ((normalizedGaugeState h hh o).symm_apply_apply _)

lemma normalizedGauge_endpoint_iff (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (z : ℝ → V → ℝ) (s : ℝ) (v : V → ℝ) :
    normalizedGaugeTrajectory h hh o z s=normalizedGaugeState h hh o v ↔ z s=v :=
  (normalizedGaugeState h hh o).injective.eq_iff

lemma normalizedGauge_zero_iff (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (z : ℝ → V → ℝ) (s : ℝ) : normalizedGaugeTrajectory h hh o z s=0 ↔ z s=0 := by
  simpa only [map_zero] using normalizedGauge_endpoint_iff h hh o z s 0

/-- Entire exact endpoint-feasible solution sets, including uniqueness, match
under the constructed state map, while the scalar control remains unchanged. -/
theorem normalizedGauge_endpoints_existsUnique_iff (h : V → ℝ) (hh : ∀ v, h v ≠ 0) (o : V)
    (A : Matrix V V ℝ) (u : ℝ → ℝ) (T : ℝ) (z0 z1 : V → ℝ) :
    (∃! z : ℝ → V → ℝ, IsForcedMatrixSolution A (Pi.single o 1) u z ∧ z 0=z0 ∧ z T=z1) ↔
      (∃! q : ℝ → V → ℝ, IsForcedMatrixSolution (diagonalGauge h A) (Pi.single o 1) u q ∧
        q 0=normalizedGaugeState h hh o z0 ∧ q T=normalizedGaugeState h hh o z1) := by
  let E := normalizedGaugeTrajectory h hh o
  have hp (z : ℝ → V → ℝ) :
      (IsForcedMatrixSolution A (Pi.single o 1) u z ∧ z 0=z0 ∧ z T=z1) ↔
      (IsForcedMatrixSolution (diagonalGauge h A) (Pi.single o 1) u (E z) ∧
        E z 0=normalizedGaugeState h hh o z0 ∧ E z T=normalizedGaugeState h hh o z1) := by
    rw [normalizedGauge_solution_iff,normalizedGauge_endpoint_iff,normalizedGauge_endpoint_iff]
  constructor
  · rintro ⟨z,hz,hu⟩
    refine ⟨E z,(hp z).mp hz,?_⟩
    intro q hq
    have hi := (hp (E.symm q)).mpr (by simpa only [Equiv.apply_symm_apply] using hq)
    have he := congrArg E (hu _ hi)
    simpa only [Equiv.apply_symm_apply] using he
  · rintro ⟨q,hq,hu⟩
    refine ⟨E.symm q,(hp (E.symm q)).mpr (by simpa only [Equiv.apply_symm_apply] using hq),?_⟩
    intro z hz
    apply E.injective
    rw [Equiv.apply_symm_apply]
    exact hu _ ((hp z).mp hz)

end HydrologyTree
