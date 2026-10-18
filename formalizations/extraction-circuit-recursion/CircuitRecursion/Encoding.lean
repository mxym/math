import CircuitRecursion.Registers

open CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def finiteEmbedding {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α≤Fintype.card β) : α ↪ β :=
  (Fintype.equivFin α).toEmbedding.trans
    ((⟨fun i => ⟨i.val,lt_of_lt_of_le i.isLt h⟩,
      fun i j hij => Fin.ext (congrArg (fun x : Fin (Fintype.card β) => x.val) hij)⟩ :
      Fin (Fintype.card α) ↪ Fin (Fintype.card β)).trans (Fintype.equivFin β).symm.toEmbedding)

def codeWires (k : ℕ) : ℕ := 2*encodingPairs k

theorem codeWires_available (k : ℕ) : codeWires k≤originalWireCount k := by
  rw [originalWireCount_eq]
  have h := encodingPairs_le_copy k
  unfold codeWires
  omega

theorem codeWires_step (k : ℕ) : codeWires (k+1)≤2+codeWires k := by
  have h := encodingPairs_step k
  unfold codeWires
  omega

noncomputable def compactEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (codeWires k) :=
  finiteEmbedding (by
    rw [occupationRank_card]
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    have h := Nat.le_pow_clog (by decide : 1<4) (occupationRank k)
    simpa only [codeWires,encodingPairs,Nat.pow_mul] using h)

def extendBits {q n : ℕ} (h : q≤n) (b : Bits q) : Bits n :=
  fun i => if hi : i.val<q then b ⟨i.val,hi⟩ else false

theorem extendBits_injective {q n : ℕ} (h : q≤n) : Function.Injective (extendBits h) := by
  intro b c he
  funext i
  have hi := congrFun he (Fin.castLE h i)
  simpa [extendBits,i.isLt] using hi

def extendEmbedding {ι : Type*} {q n : ℕ} (h : q≤n) (e : ι ↪ Bits q) : ι ↪ Bits n :=
  e.trans ⟨extendBits h,extendBits_injective h⟩

noncomputable def originalEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (originalWireCount k) :=
  extendEmbedding (codeWires_available k) (compactEncoding k)

noncomputable def nextEncoding (k : ℕ) : Sym (Fin 4) (k+1) ↪ Bits (2+codeWires k) :=
  extendEmbedding (codeWires_step k) (compactEncoding (k+1))

end CircuitRecursion
