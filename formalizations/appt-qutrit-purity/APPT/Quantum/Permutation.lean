import APPT.Quantum.Orbit
import Mathlib.Data.Fintype.Sum
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def permMatrix (e : ι ≃ ι) : Matrix ι ι ℂ := fun i j => if e i=j then 1 else 0

theorem permMatrix_mul_conjTranspose (e : ι ≃ ι) :
    permMatrix e*(permMatrix e)ᴴ=1 := by
  ext i j
  simp [permMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_ite, ite_mul, e.injective.eq_iff, eq_comm]

theorem permMatrix_conjTranspose (e : ι ≃ ι) : (permMatrix e)ᴴ = permMatrix e.symm := by
  ext i j
  simp [permMatrix, Matrix.conjTranspose_apply, e.eq_symm_apply, eq_comm]

theorem permMatrix_conjTranspose_mul (e : ι ≃ ι) :
    (permMatrix e)ᴴ*permMatrix e=1 := by
  simpa only [permMatrix_conjTranspose, Equiv.symm_symm] using
    permMatrix_mul_conjTranspose e.symm

noncomputable def permUnitary (e : ι ≃ ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨permMatrix e, by
    constructor
    · simpa only [Matrix.star_eq_conjTranspose] using permMatrix_conjTranspose_mul e
    · simpa only [Matrix.star_eq_conjTranspose] using permMatrix_mul_conjTranspose e⟩

theorem permMatrix_diagonal (e : ι ≃ ι) (d : ι → ℂ) :
    permMatrix e*Matrix.diagonal d*(permMatrix e)ᴴ =
    Matrix.diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, permMatrix, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, ite_mul, Function.comp_def, e.injective.eq_iff, eq_comm]
  split_ifs <;> simp_all

theorem embedding_extend_perm (a b : Fin 9 → ι)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ e : ι ≃ ι, ∀ i, e (a i)=b i := by
  classical
  let f : ι → ι := fun x => if h : ∃ i, a i=x then b (Classical.choose h) else b 0
  have hf : ∀ i, f (a i)=b i := by
    intro i
    dsimp only [f]
    rw [dif_pos ⟨i,rfl⟩]
    congr 1
    exact ha (Classical.choose_spec (show ∃ j, a j=a i from ⟨i,rfl⟩))
  let s : Finset ι := Finset.univ.image a
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    rw [hf,hf] at hxy
    exact congrArg a (hb hxy)
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset ι)) (s := s) (f := f) (by simp)
    (by intro x hx; simp) hinj
  let u : (Finset.univ : Finset ι) ≃ ι := Equiv.ofBijective (fun x => x.val)
    ⟨Subtype.val_injective, fun x => ⟨⟨x,Finset.mem_univ x⟩,rfl⟩⟩
  refine ⟨e.trans u,?_⟩
  intro i
  exact (he (a i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)).trans (hf i)

end APPT.Quantum
