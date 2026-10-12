import APPTReview.PurityInterval

open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Partial transpose preserves the Hilbert--Schmidt square on Hermitian matrices. -/
theorem purity_partialTranspose {A : Matrix (a × b) (a × b) ℂ} (hA : A.IsHermitian) :
    APPT.Quantum.purity (APPT.Quantum.partialTranspose A)=APPT.Quantum.purity A := by
  rw [purity_eq_entry_norm_sum (APPT.Quantum.partialTranspose_isHermitian hA),
    purity_eq_entry_norm_sum hA]
  let e : ((a × b) × (a × b)) ≃ ((a × b) × (a × b)) :=
    { toFun := fun p => ((p.2.1,p.1.2),(p.1.1,p.2.2))
      invFun := fun p => ((p.2.1,p.1.2),(p.1.1,p.2.2))
      left_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl
      right_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl }
  have hs := e.sum_comp (fun p => ‖A p.1 p.2‖^2)
  simpa [e, APPT.Quantum.partialTranspose, Fintype.sum_prod_type] using hs

/-- A Hermitian unit Hilbert--Schmidt bound implies the operator upper bound I. -/
theorem one_sub_psd_of_hermitian_purity {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) (hp : APPT.Quantum.purity A≤1) : (1-A).PosSemidef := by
  have hs : (∑ i, (hA.eigenvalues i)^2)=APPT.Quantum.purity A := by
    rw [purity_eq_ordered_eigenvalues hA]
    have he := (spectralLabel (a × b)).sum_comp (fun i => (hA.eigenvalues i)^2)
    simpa only [eigenvalues_spectralLabel] using he.symm
  have hi (i) : hA.eigenvalues i≤1 := by
    have hsq := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (hA.eigenvalues j)) (Finset.mem_univ i)
    rw [hs] at hsq
    nlinarith
  have hd : (Matrix.diagonal (fun i => ((1-hA.eigenvalues i : ℝ):ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ)≤((1-hA.eigenvalues i : ℝ):ℂ)
    exact_mod_cast (sub_nonneg.mpr (hi i))
  have hspec := hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at hspec
  have he : Matrix.diagonal (fun i => ((1-hA.eigenvalues i : ℝ):ℂ)) =
      (1 : Matrix (a × b) (a × b) ℂ)-Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hh := hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (a × b) (a × b) ℂ)
  rw [he, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hh
  simpa [← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self, ← hspec] using hh

/-- A dimension-uniform sufficient APPT ball, proved without Schmidt decomposition. -/
theorem absolutelyPPT_one_sub_of_hermitian_purity {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) (hp : APPT.Quantum.purity A≤1) :
    APPT.Quantum.AbsolutelyPPT (1-A) := by
  intro U
  let Q := (U : Matrix (a × b) (a × b) ℂ)*A*(U : Matrix (a × b) (a × b) ℂ)ᴴ
  have hQ : Q.IsHermitian := by
    simp [Q, Matrix.IsHermitian, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]
  have hpur : APPT.Quantum.purity Q≤1 := by
    dsimp [Q]
    rwa [APPT.Quantum.purity_unitaryConjugate]
  have hh := one_sub_psd_of_hermitian_purity
    (APPT.Quantum.partialTranspose_isHermitian hQ)
    (by rwa [purity_partialTranspose hQ])
  simpa [Q, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_mul_star_self] using hh

/-- In particular, the complement of every density matrix has the APPT property. -/
theorem density_complement_absolutelyPPT {A : Matrix (a × b) (a × b) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : APPT.Quantum.AbsolutelyPPT (1-A) :=
  absolutelyPPT_one_sub_of_hermitian_purity hρ.1.isHermitian (density_purity_unit_interval hρ).2

/-- Exact trace-square formula retaining the trace-one premise. -/
theorem density_one_sub_smul_purity {A : Matrix (a × b) (a × b) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (c : ℝ) :
    APPT.Quantum.purity (1-c • A)=(Fintype.card (a × b):ℝ)-2*c+c^2*APPT.Quantum.purity A := by
  have he : (1-c • A)*(1-c • A)=(1 : Matrix (a × b) (a × b) ℂ)-(2*c) • A+c^2 • (A*A) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  unfold APPT.Quantum.purity
  rw [he]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hρ.2,
    Complex.smul_re, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.one_re, smul_eq_mul]
  <;> ring

/-- Every density matrix in the standard purity ball is physically APPT. -/
theorem density_appt_of_purity_ball {m n : ℕ} (hD : 1<m*n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hρ : APPT.Quantum.IsDensity A)
    (hp : APPT.Quantum.purity A≤1/((m:ℝ)*n-1)) : APPT.Quantum.AbsolutelyPPT A := by
  let c : ℝ := (m:ℝ)*n-1
  have hDR : (1:ℝ)<(m:ℝ)*n := by exact_mod_cast hD
  have hc : 0<c := by dsimp [c]; linarith
  have hH : (1-c • A).IsHermitian :=
    Matrix.isHermitian_one.sub (hρ.1.isHermitian.smul (show IsSelfAdjoint c by rfl))
  have hsq : c^2*APPT.Quantum.purity A≤c := by
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg c)
    have he : c^2*(1/((m:ℝ)*n-1))=c := by change c^2*(1/c)=c; field_simp
    rwa [he] at hh
  have hpur : APPT.Quantum.purity (1-c • A)≤1 := by
    rw [density_one_sub_smul_purity hρ]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    dsimp [c] at *
    linarith
  have hh := absolutelyPPT_one_sub_of_hermitian_purity hH hpur
  have he : 1-(1-c • A)=c • A := by abel
  rw [he] at hh
  have hs := APPT.Quantum.absolutelyPPT_smul hh (show (0:ℝ)≤1/c by positivity)
  simpa [smul_smul, ne_of_gt hc] using hs

end APPTReview
