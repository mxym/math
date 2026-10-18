import CircuitRecursion.Encoding

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

def extendGate {q n : ℕ} (h : q≤n) : Gate q → Gate n
  | .single i U => .single (Fin.castLE h i) U
  | .cnot c t hct => .cnot (Fin.castLE h c) (Fin.castLE h t)
      (fun he => hct (Fin.ext (congrArg (fun x : Fin n => x.val) he)))

def prefixCircuit {q n : ℕ} (h : q≤n) (c : Circuit q) : Circuit n :=
  c.map (extendGate h)

theorem prefixCircuit_length {q n : ℕ} (h : q≤n) (c : Circuit q) :
    (prefixCircuit h c).length=c.length := by
  simp [prefixCircuit]

theorem extendBits_eq_pad {q r : ℕ} (h : q≤q+r) (b : Bits q) :
    extendBits h b=pad r b := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [extendBits,pad,j.isLt]
  · simp [extendBits,pad,zeroBits]

theorem prefixCircuit_eq_lift {q r : ℕ} (h : q≤q+r) (c : Circuit q) :
    prefixCircuit h c=liftCircuit r c := by
  unfold prefixCircuit liftCircuit
  apply List.map_congr_left
  intro g hg
  cases g <;> rfl

theorem extendBits_trans {q m n : ℕ} (h1 : q≤m) (h2 : m≤n) (b : Bits q) :
    extendBits h2 (extendBits h1 b)=extendBits (h1.trans h2) b := by
  funext i
  by_cases hm : i.val<m
  · simp [extendBits,hm]
  · have hq : ¬i.val<q := by omega
    simp [extendBits,hm,hq]

theorem extendBits_append {p q n : ℕ} (h : q≤n) (a : Bits p) (b : Bits q) :
    extendBits (Nat.add_le_add_left h p) (Fin.append a b)=
      Fin.append a (extendBits h b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj : j.val<p+q := by omega
    simp only [extendBits,Fin.coe_castAdd,dif_pos hj,Fin.append_left]
    change Fin.append a b (Fin.castAdd q j)=_
    simp
  · by_cases hj : j.val<q
    · have hj' : p+j.val<p+q := by omega
      simp only [extendBits,Fin.coe_natAdd,dif_pos hj',Fin.append_right,dif_pos hj]
      change Fin.append a b (Fin.natAdd p ⟨j.val,hj⟩)=_
      exact Fin.append_right a b ⟨j.val,hj⟩
    · have hj' : ¬p+j.val<p+q := by omega
      simp [extendBits,hj',hj]

theorem paddedVector {q r : ℕ} (v : Bits q → ℂ) :
    Extraction.coordinateIsometry (padEmbedding r (Function.Embedding.refl (Bits q)))*ᵥv=
      fun w => v (prefixBits w)*(Pi.single (zeroBits r) 1 : Bits r → ℂ) (suffixBits w) := by
  classical
  funext w
  change (∑ b : Bits q,(if w=pad r b then (1 : ℂ) else 0)*v b)=_
  simp only [ite_mul,one_mul,zero_mul]
  have he (b : Bits q) : pad r b=w ↔ b=prefixBits w ∧ zeroBits r=suffixBits w := by
    constructor
    · intro h
      constructor
      · funext i; simpa [pad,prefixBits] using congrFun h (Fin.castAdd r i)
      · funext i; simpa [pad,suffixBits] using congrFun h (Fin.natAdd q i)
    · rintro ⟨rfl,h⟩
      apply (splitRegister q r).injective
      change (prefixBits (pad r (prefixBits w)),suffixBits (pad r (prefixBits w)))=
        (prefixBits w,suffixBits w)
      simp only [pad,prefix_append,suffix_append,h]
  have he' (b : Bits q) : w=pad r b ↔ b=prefixBits w ∧ zeroBits r=suffixBits w := by
    rw [eq_comm]; exact he b
  simp only [he']
  by_cases hz : zeroBits r=suffixBits w <;> simp [hz,eq_comm]

theorem prefixCircuit_action {q n : ℕ} (h : q≤n) (c : Circuit q)
    (v : Bits q → ℂ) :
    run (prefixCircuit h c)
      (Extraction.coordinateIsometry (extendEmbedding h (Function.Embedding.refl (Bits q)))*ᵥv)=
      Extraction.coordinateIsometry (extendEmbedding h (Function.Embedding.refl (Bits q)))*ᵥrun c v := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
  have he : extendEmbedding h (Function.Embedding.refl (Bits q))=
      padEmbedding r (Function.Embedding.refl (Bits q)) := by
    apply Function.Embedding.ext
    intro b
    exact extendBits_eq_pad h b
  rw [prefixCircuit_eq_lift,he,paddedVector,paddedVector,run_liftCircuit]

end CircuitRecursion
