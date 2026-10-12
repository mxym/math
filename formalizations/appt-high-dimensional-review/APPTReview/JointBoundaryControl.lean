import APPTReview.JointRobust
open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- All 45 negative pair slots and 102 coordinates outside the Schmidt square. -/
def boundarySupport1038 : Finset (Fin 10 × Fin 38) :=
  Finset.univ.filter (fun p => (p.2.val<10 ∧ p.2.val<p.1.val) ∨
    (10≤p.2.val ∧ 28*p.1.val+(p.2.val-10)<102))
theorem boundarySupport1038_card : boundarySupport1038.card=147 := by decide +kernel

noncomputable def boundaryBase1038 (d : ℝ) : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ :=
  (15:ℝ) • 1+(2:ℝ) • setProjection boundarySupport1038+d • setProjection {(1,0)}
noncomputable def boundaryWeight1038 (d : ℝ) (p : Fin 10 × Fin 38) : ℝ :=
  15+2*(if p∈boundarySupport1038 then 1 else 0)+d*(if p=(1,0) then 1 else 0)

theorem boundaryBase1038_diagonal (d : ℝ) : boundaryBase1038 d=
    Matrix.diagonal (fun p => (boundaryWeight1038 d p:ℂ)) := by
  ext p q
  by_cases hpq : p=q
  · subst q
    simp [boundaryBase1038,boundaryWeight1038,setProjection,Matrix.diagonal_apply,
      Matrix.one_apply,Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  · simp [boundaryBase1038,setProjection,Matrix.diagonal_apply,Matrix.one_apply,hpq]

theorem boundaryBase1038_trace (d : ℝ) : (boundaryBase1038 d).trace=(5994+d:ℝ) := by
  norm_num [boundaryBase1038,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,
    setProjection_trace,boundarySupport1038_card,Complex.real_smul]

/-- Increasing the top eigenvalue from 41 to 42 fails at an actual quantum witness. -/
theorem boundaryBase1038_25_not_appt : ¬ APPT.Quantum.AbsolutelyPPT (boundaryBase1038 25) := by
  intro h
  rw [boundaryBase1038_diagonal] at h
  let e : Fin 10 → Fin 38 := Fin.castLE (by omega)
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin 38 => z.val) hij)
  have hm := diagonal_appt_witness_posSemidef (boundaryWeight1038 25) h e he
  have hq := hm.dotProduct_mulVec_nonneg (fun i : Fin 10 => if i.val<2 then (4:ℝ) else 1)
  norm_num [dotProduct,Matrix.mulVec,witnessMatrix,boundaryWeight1038,boundarySupport1038,
    Fin.sum_univ_succ,e] at hq

noncomputable def boundaryPerturbation1038 : Matrix (Fin 10 × Fin 38) (Fin 10 × Fin 38) ℂ :=
  (1/6019:ℝ) • boundaryBase1038 25

theorem boundaryPerturbation1038_density : APPT.Quantum.IsDensity boundaryPerturbation1038 := by
  constructor
  · have hp := hermitian_idempotent_posSemidef (setProjection boundarySupport1038)
      (setProjection_hermitian _) (setProjection_sq _)
    have hr := hermitian_idempotent_posSemidef (setProjection ({(1,0)}:Finset (Fin 10 × Fin 38)))
      (setProjection_hermitian _) (setProjection_sq _)
    exact (((Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ)≤15)).add
      (hp.smul (by norm_num : (0:ℝ)≤2))).add
      (hr.smul (by norm_num : (0:ℝ)≤25))).smul (by norm_num : (0:ℝ)≤1/6019)
  · norm_num [boundaryPerturbation1038,Matrix.trace_smul,boundaryBase1038_trace,Complex.real_smul]

theorem boundaryPerturbation1038_not_appt : ¬ APPT.Quantum.AbsolutelyPPT boundaryPerturbation1038 := by
  intro h
  have hh := APPT.Quantum.absolutelyPPT_smul h (by norm_num : (0:ℝ)≤6019)
  have he : (6019:ℝ) • boundaryPerturbation1038=boundaryBase1038 25 := by
    unfold boundaryPerturbation1038
    module
  rw [he] at hh
  exact boundaryBase1038_25_not_appt hh

end APPTReview
