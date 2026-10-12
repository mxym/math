import CofactorSortCoordinates
import CofactorHarmonicBound

/-! Binary subset bounds imply a bound for every nonnegative finite real vector. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def zeroExtend {n : ℕ} (u : Fin n → E) (j : ℕ) : E :=
  if h : j < n then u ⟨j,h⟩ else 0

def prefixSet (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)

theorem sum_zeroExtend_prefix {n k : ℕ} (u : Fin n → E) (hk : k ≤ n) :
    (∑ j ∈ Finset.range k, zeroExtend u j) = ∑ i ∈ prefixSet n k, u i := by
  classical
  refine Finset.sum_bij (fun j hj => (⟨j,lt_of_lt_of_le (Finset.mem_range.mp hj) hk⟩ : Fin n))
    ?_ ?_ ?_ ?_
  · intro j hj
    simp [prefixSet, Finset.mem_range.mp hj]
  · intro j hj l hl h
    exact congrArg Fin.val h
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨i.val,Finset.mem_range.mpr h,Fin.ext rfl⟩
  · intro j hj
    simp [zeroExtend, lt_of_lt_of_le (Finset.mem_range.mp hj) hk]

theorem card_prefixSet (n k : ℕ) (hk : k ≤ n) : (prefixSet n k).card = k := by
  classical
  have hc : (Finset.range k).card = (prefixSet n k).card := by
    refine Finset.card_bij
      (fun j hj => (⟨j,lt_of_lt_of_le (Finset.mem_range.mp hj) hk⟩ : Fin n)) ?_ ?_ ?_
    · intro j hj
      simp [prefixSet, Finset.mem_range.mp hj]
    · intro j hj l hl h
      exact congrArg Fin.val h
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      exact ⟨i.val,Finset.mem_range.mpr h,Fin.ext rfl⟩
  simpa using hc.symm

theorem sum_zeroExtend {n : ℕ} (u : Fin n → E) :
    (∑ j ∈ Finset.range n, zeroExtend u j) = ∑ i, u i := by
  rw [sum_zeroExtend_prefix u le_rfl]
  have hp : prefixSet n n = Finset.univ := by
    ext i
    simp [prefixSet,i.isLt]
  rw [hp]

theorem zeroExtend_smul {n : ℕ} (x : Fin n → ℝ) (u : Fin n → E) (j : ℕ) :
    zeroExtend x j • zeroExtend u j = zeroExtend (fun i => x i • u i) j := by
  unfold zeroExtend
  split <;> simp

theorem zeroExtend_sq {n : ℕ} (x : Fin n → ℝ) (j : ℕ) :
    zeroExtend x j ^ 2 = zeroExtend (fun i => x i ^ 2) j := by
  unfold zeroExtend
  split <;> simp

theorem antitone_nonneg_binary_norm_bound {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (hx : Antitone x) (hn : ∀ i, 0 ≤ x i)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, x i • u i‖^2 ≤ binaryNormConstant n * ∑ i, x i ^ 2 := by
  have h := sorted_binary_norm_bound (zeroExtend u) (zeroExtend x) n
    (by simp [zeroExtend]) ?_ ?_
  · simpa only [zeroExtend_smul, zeroExtend_sq, sum_zeroExtend] using h
  · intro j hj
    have hlt : j < n := hj
    by_cases hnext : j+1 < n
    · simp only [zeroExtend, dif_pos hlt, dif_pos hnext]
      exact sub_nonneg.mpr (hx (show (⟨j,hlt⟩ : Fin n) ≤ ⟨j+1,hnext⟩ by simp))
    · simpa [zeroExtend,hlt,hnext] using hn ⟨j,hlt⟩
  · intro j hj
    have hk : j+1 ≤ n := Nat.succ_le_of_lt hj
    rw [sum_zeroExtend_prefix u hk]
    simpa only [card_prefixSet n (j+1) hk, Nat.cast_add, Nat.cast_one] using hu (prefixSet n (j+1))

theorem nonneg_binary_norm_bound {n : ℕ} (u : Fin n → E) (x : Fin n → ℝ)
    (hn : ∀ i, 0 ≤ x i)
    (hu : ∀ s : Finset (Fin n), ‖∑ i ∈ s, u i‖ ≤ Real.sqrt s.card) :
    ‖∑ i, x i • u i‖^2 ≤ binaryNormConstant n * ∑ i, x i ^ 2 := by
  classical
  obtain ⟨σ,hσ⟩ := exists_antitone_permutation n x
  have h := antitone_nonneg_binary_norm_bound (fun i => u (σ i)) (fun i => x (σ i))
    hσ (fun i => hn (σ i)) ?_
  · convert h using 1
    · rw [← Fintype.sum_equiv σ (fun i => x (σ i) • u (σ i)) (fun i => x i • u i)]
      intro i
      rfl
    · rw [← Fintype.sum_equiv σ (fun i => x (σ i) ^ 2) (fun i => x i ^ 2)]
      intro i
      rfl
  · intro s
    have hsum : (∑ i ∈ s, u (σ i)) = ∑ i ∈ s.map σ.toEmbedding, u i :=
      (Finset.sum_map s σ.toEmbedding u).symm
    rw [hsum]
    simpa only [Finset.card_map] using hu (s.map σ.toEmbedding)

end
end CofactorSpectral
