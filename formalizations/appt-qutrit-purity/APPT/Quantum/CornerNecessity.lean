import APPT.Quantum.ExtendedConjugate
import APPT.Quantum.CornerHadamard
import APPT.Quantum.RealPSD
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

/-- The physical three-by-three product-basis corner. -/
def cornerEmbedding (a : Fin 3 → b) : Fin 3 × Fin 3 → Fin 3 × b :=
  fun i => (i.1,a i.2)

theorem cornerEmbedding_injective (a : Fin 3 → b) (ha : Function.Injective a) :
    Function.Injective (cornerEmbedding a) := by
  intro i j h
  change (i.1,a i.2)=(j.1,a j.2) at h
  apply Prod.ext
  · exact congrArg (fun z : Fin 3 × b => z.1) h
  · exact ha (congrArg Prod.snd h)

noncomputable def cornerResponse (slot : Fin 3 × Fin 3 → Fin 9) (y : Fin 9 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (cornerHadamard*cornerDiagonal slot y*cornerHadamardᴴ) (j,i) (i,j)

/-- Any nine chosen diagonal eigenvalues give a PSD corner response after a physical
unitary conjugation. The quantifier is the actual global APPT condition. -/
theorem selected_corner_posSemidef (a : Fin 3 → b) (ha : Function.Injective a)
    (mu : Fin 3 × b → ℝ) (x : Fin 9 → Fin 3 × b) (hx : Function.Injective x)
    (h : AbsolutelyPPT (Matrix.diagonal (fun i => (mu i : ℂ))))
    (slot : Fin 3 × Fin 3 → Fin 9) (hslot : Function.Bijective slot) :
    (cornerResponse slot (mu ∘ x)).PosSemidef := by
  classical
  let e := cornerEmbedding a
  have he : Function.Injective e := cornerEmbedding_injective a ha
  let S : (Fin 3 × Fin 3) ≃ Fin 9 := Equiv.ofBijective slot hslot
  let pos : Fin 9 → Fin 3 × b := e ∘ S.symm
  have hpos : Function.Injective pos := he.comp S.symm.injective
  obtain ⟨sigma,hsigma⟩ := embedding_extend_perm pos x hpos hx
  have hassign : ∀ q, sigma (e q)=x (slot q) := by
    intro q
    have hh := hsigma (S q)
    calc
      sigma (e q) = x (S q) := by simpa [pos, Function.comp_def] using hh
      _ = x (slot q) := rfl
  have hp := absolutelyPPT_conjugate h (permUnitary sigma)
  have hd : AbsolutelyPPT (Matrix.diagonal (fun i => (mu (sigma i) : ℂ))) := by
    simpa only [permUnitary, permMatrix_diagonal, Function.comp_def] using hp
  let W := extendedUnitary e he cornerUnitary
  have hw := (hd W).submatrix (fun i : Fin 3 => (i,a i))
  have heq : (partialTranspose ((W : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*
      Matrix.diagonal (fun i => (mu (sigma i) : ℂ))*
      (W : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ)).submatrix
      (fun i : Fin 3 => (i,a i)) (fun i : Fin 3 => (i,a i)) =
      cornerResponse slot (mu ∘ x) := by
    ext i j
    change ((extendedUnitary e he cornerUnitary : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)*
      Matrix.diagonal (fun i => (mu (sigma i) : ℂ))*
      (extendedUnitary e he cornerUnitary : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ)
      (e (j,i)) (e (i,j)) = _
    rw [extendedUnitary_conjugate_entry]
    simp only [cornerUnitary, cornerResponse, cornerDiagonal, Function.comp_def, hassign]
  rwa [heq] at hw

/-- Actual APPT implies Hildebrand's two necessary qutrit matrices.
The converse is not used or assumed. -/
theorem diagonal_appt_necessary_matrices (a : Fin 3 → b) (ha : Function.Injective a)
    (mu : Fin 3 × b → ℝ) (x : Fin 9 → Fin 3 × b) (hx : Function.Injective x)
    (h : AbsolutelyPPT (Matrix.diagonal (fun i => (mu i : ℂ)))) :
    (matA (mu ∘ x)).PosSemidef ∧ (matB (mu ∘ x)).PosSemidef := by
  have hA := selected_corner_posSemidef a ha mu x hx h slotA slotA_bijective
  have hB := selected_corner_posSemidef a ha mu x hx h slotB slotB_bijective
  have heA : (2 : ℝ) • cornerResponse slotA (mu ∘ x) =
      (matA (mu ∘ x)).map Complex.ofReal := by
    ext i j
    exact corner_A_entry (mu ∘ x) i j
  have heB : (2 : ℝ) • cornerResponse slotB (mu ∘ x) =
      (matB (mu ∘ x)).map Complex.ofReal := by
    ext i j
    exact corner_B_entry (mu ∘ x) i j
  constructor
  · apply real_posSemidef_of_complex
    rw [← heA]
    exact hA.smul (by norm_num : (0 : ℝ) ≤ 2)
  · apply real_posSemidef_of_complex
    rw [← heB]
    exact hB.smul (by norm_num : (0 : ℝ) ≤ 2)

end APPT.Quantum
