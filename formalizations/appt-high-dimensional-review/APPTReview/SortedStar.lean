import APPTReview.CornerSort

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A positive pivot follows from trace one and the sorted physical rank-two test.
This does not presume strict positivity of every eigenvalue. -/
theorem ordered_pivot_positive {D : ℕ} (hD : 4 ≤ D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i, f i) = 1)
    (hc : f (rankTwoLabels hD (1,0)) ≤
      f (rankTwoLabels hD (0,0)) + f (rankTwoLabels hD (0,1)) +
      f (rankTwoLabels hD (1,1)))
    (k : Fin D) (hk : k.val ≤ D-3) : 0 < f k := by
  by_contra hn
  have hn' : f k ≤ 0 := le_of_not_gt hn
  have hlast : f (rankTwoLabels hD (0,0)) ≤ f k := by
    apply hf
    change k.val ≤ D-1
    omega
  have hsecond : f (rankTwoLabels hD (0,1)) ≤ f k := by
    apply hf
    change k.val ≤ D-2
    omega
  have hthird : f (rankTwoLabels hD (1,1)) ≤ f k := by
    apply hf
    exact hk
  have hzero : f (rankTwoLabels hD (1,0)) ≤ 0 := by linarith
  have hall (i : Fin D) : f i ≤ 0 :=
    (hf (by change 0 ≤ i.val; omega)).trans hzero
  have hsum : (∑ i, f i) ≤ 0 := Finset.sum_nonpos (fun i _ => hall i)
  linarith

/-- The stronger least-diagonal Schmidt-star test for canonically ordered actual
APPT eigenvalues. The finite placement permutation and every leaf-pair orientation
are constructed; no graph inequality or spectral feasibility premise is assumed. -/
theorem appt_sorted_shifted_star {h n : ℕ} (hh : 1 ≤ h) (hmn : h+1 ≤ n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (hD : 3*h+1 ≤ Fintype.card (Fin (h+1) × Fin n)) :
    let lam := hρ.1.isHermitian.eigenvalues₀
    let pivot : Fin (Fintype.card (Fin (h+1) × Fin n)) :=
      ⟨Fintype.card (Fin (h+1) × Fin n)-(2*h+1), by omega⟩
    (∑ i : Fin h,
      (lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
       lam (starSlotLabel hD (.inr (.inr (.inl i)))))^2) ≤
      4*lam (starSlotLabel hD (.inl ()))*lam pivot := by
  classical
  dsimp only
  let lam := hρ.1.isHermitian.eigenvalues₀
  let pivot : Fin (Fintype.card (Fin (h+1) × Fin n)) :=
    ⟨Fintype.card (Fin (h+1) × Fin n)-(2*h+1), by omega⟩
  have hfour : 4 ≤ Fintype.card (Fin (h+1) × Fin n) := by omega
  have ht : 0 < lam pivot := ordered_pivot_positive hfour lam
    hρ.1.isHermitian.eigenvalues₀_antitone (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear (by omega) hmn hρ.1.isHermitian happt hfour)
    pivot (by dsimp [pivot]; omega)
  let e : Fin (h+1) → Fin n := Fin.castLE hmn
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hab)
  let emb : Fin (h+1) × Fin (h+1) → Fin (h+1) × Fin n :=
    fun p => (p.1,e p.2)
  have hemb : Function.Injective emb := by
    intro a b hab
    exact Prod.ext (congrArg (fun p : Fin (h+1) × Fin n => p.1) hab)
      (he (congrArg (fun p : Fin (h+1) × Fin n => p.2) hab))
  let slots : StarSlot h → Fin (h+1) × Fin n := fun s => emb (starSlotCoord s)
  let targets : StarSlot h → Fin (h+1) × Fin n :=
    fun s => spectralLabel _ (starSlotLabel hD s)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair slots targets
    (hemb.comp starSlotCoord_injective)
    ((spectralLabel _).injective.comp (starSlotLabel_injective hD))
  let d : Fin (h+1) × Fin (h+1) → ℝ :=
    fun p => hρ.1.isHermitian.eigenvalues (σ (emb p))
  let cs := cornerSort (0 : Fin (h+1)) d
  obtain ⟨τ,hτ⟩ := Equiv.Perm.exists_extending_pair emb
    (fun p => σ (emb (cs p))) hemb (σ.injective.comp (hemb.comp cs.injective))
  have hfix (s : StarSlot h) : cs (starSlotCoord s) = starSlotCoord s := by
    rcases s with s | s | s | s <;> simp [cs, starSlotCoord, pairSortFun, pairBad]
  have heval (s : StarSlot h) :
      hρ.1.isHermitian.eigenvalues (τ (emb (starSlotCoord s))) = lam (starSlotLabel hD s) := by
    rw [hτ, hfix]
    change hρ.1.isHermitian.eigenvalues (σ (slots s)) = _
    rw [hσ]
    exact eigenvalues_spectralLabel hρ.1.isHermitian _
  have hc : hρ.1.isHermitian.eigenvalues (τ (0,e 0)) ≤ lam (starSlotLabel hD (.inl ())) := by
    exact (heval (.inl ())).le
  have hd (i : Fin h) : hρ.1.isHermitian.eigenvalues (τ (i.succ,e i.succ)) ≤ lam pivot := by
    rw [show hρ.1.isHermitian.eigenvalues (τ (i.succ,e i.succ)) =
      lam (starSlotLabel hD (.inr (.inl i))) from heval (.inr (.inl i))]
    apply hρ.1.isHermitian.eigenvalues₀_antitone
    change Fintype.card (Fin (h+1) × Fin n)-(2*h+1) ≤
      Fintype.card (Fin (h+1) × Fin n)-(h+2+i.val)
    omega
  have ho (i j : Fin (h+1)) (hij : i < j) :
      hρ.1.isHermitian.eigenvalues (τ (i,e j)) ≤
      hρ.1.isHermitian.eigenvalues (τ (j,e i)) := by
    by_cases hi : i=0
    · subst i
      have hj : j ≠ 0 := ne_of_gt hij
      obtain ⟨q,rfl⟩ := Fin.eq_succ_of_ne_zero hj
      rw [show hρ.1.isHermitian.eigenvalues (τ (0,e q.succ)) =
        lam (starSlotLabel hD (.inr (.inr (.inl q)))) from heval (.inr (.inr (.inl q))),
        show hρ.1.isHermitian.eigenvalues (τ (q.succ,e 0)) =
        lam (starSlotLabel hD (.inr (.inr (.inr q)))) from heval (.inr (.inr (.inr q)))]
      apply hρ.1.isHermitian.eigenvalues₀_antitone
      change q.val ≤ Fintype.card (Fin (h+1) × Fin n)-(2+q.val)
      omega
    · have hj : j ≠ 0 := by intro hj; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
      change hρ.1.isHermitian.eigenvalues (τ (emb (i,j))) ≤
        hρ.1.isHermitian.eigenvalues (τ (emb (j,i)))
      rw [hτ,hτ]
      exact cornerSort_order 0 d i j hi hj hij
  have hb := appt_eigenvalue_star_bound hρ.1.isHermitian happt τ e he
    (lam (starSlotLabel hD (.inl ()))) (lam pivot) ht hc hd ho
  have hedge (i : Fin h) :
      hρ.1.isHermitian.eigenvalues (τ (i.succ,e 0)) -
      hρ.1.isHermitian.eigenvalues (τ (0,e i.succ)) =
      lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
      lam (starSlotLabel hD (.inr (.inr (.inl i)))) := by
    rw [show hρ.1.isHermitian.eigenvalues (τ (i.succ,e 0)) =
      lam (starSlotLabel hD (.inr (.inr (.inr i)))) from heval (.inr (.inr (.inr i))),
      show hρ.1.isHermitian.eigenvalues (τ (0,e i.succ)) =
      lam (starSlotLabel hD (.inr (.inr (.inl i)))) from heval (.inr (.inr (.inl i)))]
  simp_rw [hedge] at hb
  exact hb

end APPTReview
