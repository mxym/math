import CPInterface.PPT

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace ExtractionLOCC
noncomputable section

/-- A finite adaptive local-instrument tree. Each publicly communicated outcome
selects both the next instrument and the acting party's next local dimension.
The individual Kraus outcomes may refine a coarser classical outcome. -/
inductive Tree (c d : ℕ) : ℕ → ℕ → Type where
  | done : Tree c d c d
  | alice {a b : ℕ} (r : ℕ) (next : Fin r → ℕ)
      (A : (i : Fin r) → Matrix (Fin (next i)) (Fin a) ℂ)
      (complete : ∑ i, (A i)ᴴ * A i = 1)
      (cont : (i : Fin r) → Tree c d (next i) b) : Tree c d a b
  | bob {a b : ℕ} (r : ℕ) (next : Fin r → ℕ)
      (B : (i : Fin r) → Matrix (Fin (next i)) (Fin b) ℂ)
      (complete : ∑ i, (B i)ᴴ * B i = 1)
      (cont : (i : Fin r) → Tree c d a (next i)) : Tree c d a b

namespace Tree
variable {a b c d : ℕ}

/-- A leaf is exactly the full communicated classical history. -/
def Leaf : {a b : ℕ} → Tree c d a b → Type
  | _, _, .done => PUnit
  | _, _, .alice r _ _ _ f => (i : Fin r) × Leaf (f i)
  | _, _, .bob r _ _ _ f => (i : Fin r) × Leaf (f i)

@[instance_reducible] def leafFintype : {a b : ℕ} → (T : Tree c d a b) → Fintype T.Leaf
  | _, _, .done => inferInstanceAs (Fintype PUnit)
  | _, _, .alice _ _ _ _ f => by
      letI : ∀ i, Fintype (Leaf (f i)) := fun i => leafFintype (f i)
      exact inferInstanceAs (Fintype (Sigma (fun i => Leaf (f i))))
  | _, _, .bob _ _ _ _ f => by
      letI : ∀ i, Fintype (Leaf (f i)) := fun i => leafFintype (f i)
      exact inferInstanceAs (Fintype (Sigma (fun i => Leaf (f i))))

instance (T : Tree c d a b) : Fintype T.Leaf := T.leafFintype

def leafAlice : {a b : ℕ} → (T : Tree c d a b) → T.Leaf → Matrix (Fin c) (Fin a) ℂ
  | _, _, .done, _ => 1
  | _, _, .alice _ _ A _ f, h => leafAlice (f h.1) h.2 * A h.1
  | _, _, .bob _ _ _ _ f, h => leafAlice (f h.1) h.2

def leafBob : {a b : ℕ} → (T : Tree c d a b) → T.Leaf → Matrix (Fin d) (Fin b) ℂ
  | _, _, .done, _ => 1
  | _, _, .alice _ _ _ _ f, h => leafBob (f h.1) h.2
  | _, _, .bob _ _ B _ f, h => leafBob (f h.1) h.2 * B h.1

/-- Every actual leaf operator factors into Alice's and Bob's ordered local
operators. Adaptivity is retained in the dependent leaf/history index. -/
def leafKraus (T : Tree c d a b) (h : T.Leaf) :
    Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ :=
  T.leafAlice h ⊗ₖ T.leafBob h

theorem leafKraus_alice (r : ℕ) (next : Fin r → ℕ)
    (A : (i : Fin r) → Matrix (Fin (next i)) (Fin a) ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (f : (i : Fin r) → Tree c d (next i) b)
    (i : Fin r) (h : (f i).Leaf) :
    (Tree.alice r next A hA f).leafKraus ⟨i,h⟩ =
      (f i).leafKraus h * (A i ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) := by
  simp only [leafKraus, leafAlice, leafBob, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem leafKraus_bob (r : ℕ) (next : Fin r → ℕ)
    (B : (i : Fin r) → Matrix (Fin (next i)) (Fin b) ℂ)
    (hB : ∑ i, (B i)ᴴ * B i = 1) (f : (i : Fin r) → Tree c d a (next i))
    (i : Fin r) (h : (f i).Leaf) :
    (Tree.bob r next B hB f).leafKraus ⟨i,h⟩ =
      (f i).leafKraus h * ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ B i) := by
  simp only [leafKraus, leafAlice, leafBob, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem gram_precompose {ι μ ο κ : Type} [Fintype ι] [Fintype μ] [Fintype ο]
    [Fintype κ] (C : κ → Matrix ο μ ℂ) (L : Matrix μ ι ℂ) :
    (∑ j, (C j * L)ᴴ * (C j * L)) = Lᴴ * (∑ j, (C j)ᴴ * C j) * L := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem leafKraus_complete (T : Tree c d a b) :
    ∑ h, (T.leafKraus h)ᴴ * T.leafKraus h = 1 := by
  induction T with
  | done =>
      change (∑ _h : PUnit, ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ * (1 ⊗ₖ 1)) = 1
      simp
  | @alice a b r next A hA f ih =>
      change (∑ h : (i : Fin r) × (f i).Leaf, _) = _
      rw [Fintype.sum_sigma]
      simp_rw [leafKraus_alice, gram_precompose, ih, Matrix.mul_one,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
      have hs : (∑ i, ((A i)ᴴ * A i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) =
          (∑ i, (A i)ᴴ * A i) ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) := by
        ext x y
        simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
      rw [hs, hA, Matrix.one_kronecker_one]
  | @bob a b r next B hB f ih =>
      change (∑ h : (i : Fin r) × (f i).Leaf, _) = _
      rw [Fintype.sum_sigma]
      simp_rw [leafKraus_bob, gram_precompose, ih, Matrix.mul_one,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
      have hs : (∑ i, (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ ((B i)ᴴ * B i)) =
          (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ (∑ i, (B i)ᴴ * B i) := by
        ext x y
        simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
      rw [hs, hB, Matrix.one_kronecker_one]

/-- The actual channel denotes the sum over all communicated histories. -/
def channel (T : Tree c d a b) := ExtractionCP.krausLinearMap T.leafKraus

theorem channel_completelyPositive (T : Tree c d a b) :
    ExtractionCP.CompletelyPositive T.channel :=
  ExtractionCP.krausLinearMap_completelyPositive _

theorem channel_tracePreserving (T : Tree c d a b) :
    ExtractionCP.TracePreserving T.channel :=
  Extraction.krausApply_trace _ T.leafKraus_complete

theorem krausApply_precompose {ι μ ο κ : Type} [Fintype ι] [Fintype μ] [Fintype ο]
    [Fintype κ] (C : κ → Matrix ο μ ℂ) (L : Matrix μ ι ℂ)
    (X : Matrix ι ι ℂ) :
    Extraction.krausApply (fun j => C j * L) X = Extraction.krausApply C (L * X * Lᴴ) := by
  simp only [Extraction.krausApply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem channel_done (X : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    (Tree.done : Tree c d c d).channel X = X := by
  change (∑ _h : PUnit, (1 ⊗ₖ 1) * X * (1 ⊗ₖ 1)ᴴ) = X
  simp

theorem channel_alice (r : ℕ) (next : Fin r → ℕ)
    (A : (i : Fin r) → Matrix (Fin (next i)) (Fin a) ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (f : (i : Fin r) → Tree c d (next i) b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (Tree.alice r next A hA f).channel X =
      ∑ i, (f i).channel ((A i ⊗ₖ 1) * X * (A i ⊗ₖ 1)ᴴ) := by
  change (∑ h : (i : Fin r) × (f i).Leaf, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ h : (f i).Leaf, _) = _
  simp_rw [leafKraus_alice]
  exact krausApply_precompose _ _ _

theorem channel_bob (r : ℕ) (next : Fin r → ℕ)
    (B : (i : Fin r) → Matrix (Fin (next i)) (Fin b) ℂ)
    (hB : ∑ i, (B i)ᴴ * B i = 1) (f : (i : Fin r) → Tree c d a (next i))
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (Tree.bob r next B hB f).channel X =
      ∑ i, (f i).channel ((1 ⊗ₖ B i) * X * (1 ⊗ₖ B i)ᴴ) := by
  change (∑ h : (i : Fin r) × (f i).Leaf, _) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ h : (f i).Leaf, _) = _
  simp_rw [leafKraus_bob]
  exact krausApply_precompose _ _ _

/-- On each communicated history, partial transpose conjugates Alice's local
operator, retaining Bob's operator and every adaptive branch. -/
def ptLeafKraus (T : Tree c d a b) (h : T.Leaf) :=
  SpectralProtocol.conjugateMatrix (T.leafAlice h) ⊗ₖ T.leafBob h

theorem pt_identity (T : Tree c d a b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    APPT.Quantum.partialTranspose (T.channel (APPT.Quantum.partialTranspose X)) =
      Extraction.krausApply T.ptLeafKraus X := by
  change APPT.Quantum.partialTranspose
    (Extraction.krausApply T.leafKraus (APPT.Quantum.partialTranspose X)) = _
  ext p q
  simp only [Extraction.krausApply, Matrix.sum_apply, APPT.Quantum.partialTranspose]
  apply Finset.sum_congr rfl
  intro h _
  exact congrFun (congrFun
    (SpectralProtocol.product_congruence_partialTranspose (T.leafAlice h) (T.leafBob h) X) p) q

theorem pt_channel (T : Tree c d a b) :
    ExtractionCP.ptConjugate T.channel = ExtractionCP.krausLinearMap T.ptLeafKraus := by
  ext X p q
  exact congrFun (congrFun (T.pt_identity X) p) q

theorem channel_pt_completelyPositive (T : Tree c d a b) :
    ExtractionCP.CompletelyPositive (ExtractionCP.ptConjugate T.channel) := by
  rw [T.pt_channel]
  exact ExtractionCP.krausLinearMap_completelyPositive _

theorem ptLeafKraus_complete (T : Tree c d a b) :
    ∑ h, (T.ptLeafKraus h)ᴴ * T.ptLeafKraus h = 1 := by
  apply ExtractionCP.kraus_complete_of_tracePreserving
  intro X
  rw [← T.pt_identity X]
  exact T.channel_tracePreserving.ptConjugate X

end Tree
end
end ExtractionLOCC
