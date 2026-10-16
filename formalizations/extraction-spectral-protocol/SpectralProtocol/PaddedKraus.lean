import SpectralProtocol.SectorKraus

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {κ η V W : Type*} [Fintype κ] [Fintype η]
  [Zero V] [AddCommMonoid W]

/-- Actual zero extension of a finite family along an injection. -/
noncomputable def extendByZero (f : κ ↪ η) (A : κ → V) (j : η) : V := by
  classical
  exact if h : ∃ i,f i=j then A (Classical.choose h) else 0

theorem extendByZero_apply (f : κ ↪ η) (A : κ → V) (i : κ) :
    extendByZero f A (f i)=A i := by
  classical
  have h : ∃ j,f j=f i := ⟨i,rfl⟩
  rw [extendByZero,dif_pos h]
  exact congrArg A (f.injective (Classical.choose_spec h))

theorem extendByZero_outside (f : κ ↪ η) (A : κ → V) (j : η)
    (hj : j ∉ Set.range f) : extendByZero f A j=0 := by
  classical
  rw [extendByZero,dif_neg]
  rintro ⟨i,hi⟩
  exact hj ⟨i,hi⟩

/-- The exact finite sum after zero extension, even for nonlinear functions
that preserve zero. In particular this covers the Kraus adjoint products. -/
theorem sum_extendByZero (f : κ ↪ η) (A : κ → V) (g : V → W) (hg : g 0=0) :
    (∑ j,g (extendByZero f A j))=∑ i,g (A i) := by
  classical
  have hs : (∑ j ∈ Finset.univ.image f,g (extendByZero f A j))=
      ∑ j : η,g (extendByZero f A j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hnot : j ∉ Set.range f := by
      rintro ⟨i,rfl⟩
      exact hj (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [extendByZero_outside f A j hnot,hg]
  rw [← hs,Finset.sum_image (by intro i _ j _ hij;exact f.injective hij)]
  simp only [extendByZero_apply]

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

theorem extendByZero_kraus_complete (f : κ ↪ η) (A : κ → Matrix ο ι ℂ)
    (hA : ∑ j,(A j)ᴴ*A j=1) :
    ∑ j,(extendByZero f A j)ᴴ*extendByZero f A j=1 := by
  rw [sum_extendByZero f A (fun X => Xᴴ*X) (by simp)]
  exact hA

theorem extendByZero_krausApply (f : κ ↪ η) (A : κ → Matrix ο ι ℂ)
    (X : Matrix ι ι ℂ) :
    Extraction.krausApply (extendByZero f A) X=Extraction.krausApply A X := by
  exact sum_extendByZero f A (fun Y => Y*X*Yᴴ) (by simp)


/-- Padding either local Kraus index family with genuine zero operators does
not change the actual product channel on any complex input matrix. -/
theorem productKraus_extendByZero {γ θ β π : Type*}
    [Fintype γ] [Fintype θ] [Fintype β] [Fintype π]
    [DecidableEq β] [DecidableEq π]
    (f : κ ↪ η) (g : γ ↪ θ)
    (A : κ → Matrix ο ι ℂ) (B : γ → Matrix π β ℂ)
    (X : Matrix (ι×β) (ι×β) ℂ) :
    Extraction.krausApply (Extraction.productKraus (extendByZero f A) (extendByZero g B)) X=
      Extraction.krausApply (Extraction.productKraus A B) X := by
  unfold Extraction.krausApply Extraction.productKraus
  simp only [Fintype.sum_prod_type]
  rw [sum_extendByZero f A
    (fun Y => ∑ j : θ,(Y ⊗ₖ extendByZero g B j)*X*(Y ⊗ₖ extendByZero g B j)ᴴ)
    (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_extendByZero g B
    (fun Y => (A i ⊗ₖ Y)*X*(A i ⊗ₖ Y)ᴴ) (by simp)

end SpectralProtocol