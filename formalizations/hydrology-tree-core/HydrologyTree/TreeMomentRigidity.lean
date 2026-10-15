import HydrologyTree.TreeMatrixSupport
import HydrologyTree.BalanceWeights

/-! Exact recovery from the first two diagonal matrix moments. Tree support and
leaf elimination are proved explicitly. No simple-spectrum, full-mode, or
Jacobian-regularity assumption is made. -/
open Matrix
noncomputable section
namespace HydrologyTree

/-- A symmetric zero-diagonal tree-supported matrix is determined by its row
sums. The proof eliminates the highest remaining vertex, at arbitrary size. -/
theorem tree_symmetric_zero_nonroot_row_sums {n : ℕ} (t : OrderedTree n) (M : TreeMatrix n)
    (hs : ∀ i j, M i j=M j i) (hd : ∀ i, M i i=0)
    (hT : HasTreeMatrixSupport t M) (hr : ∀ e : Fin n, (∑ j, M e.succ j)=0) : M=0 := by
  have he : ∀ e : Fin n, M e.succ (t.parent e)=0 := by
    intro e
    induction e using (measure (fun e : Fin n => n-e.val)).wf.induction with
    | h e ih =>
      have hz : ∀ v : Fin (n+1), v ≠ t.parent e → M e.succ v=0 := by
        intro v hv
        by_cases hve : e.succ=v
        · subst v
          exact hd _
        by_cases ha : (orderedTreeGraph t).Adj e.succ v
        · rcases (orderedGraph_adj_parent_iff _ _ _).mp ha with h | h
          · let f := v.pred h.1
            have hf : f.succ=v := Fin.succ_pred v h.1
            have hp : t.parent f=e.succ := by
              have hh := h.2
              rw [← hf] at hh
              exact hh
            have hlt : n-f.val < n-e.val := by
              have hle := t.parent_le f
              rw [hp] at hle
              have hfv := f.isLt
              have hev := e.isLt
              simp only [Fin.val_succ] at hle
              omega
            rw [hs,← hf,← hp]
            exact ih f hlt
          · have hp : t.parent e=v := h.2
            exact False.elim (hv hp.symm)
        · exact hT _ _ hve ha
      have hrow := hr e
      rw [Finset.sum_eq_single (t.parent e)] at hrow
      · exact hrow
      · intro j _ hj
        exact hz j hj
      · simp
  ext i j
  change M i j=0
  by_cases hij : i=j
  · subst j
    exact hd _
  by_cases ha : (orderedTreeGraph t).Adj i j
  · obtain ⟨e,h | h⟩ := ha
    · rcases h with ⟨rfl,rfl⟩
      rw [hs]
      exact he e
    · rcases h with ⟨rfl,rfl⟩
      exact he e
  · exact hT i j hij ha

/-- The diagonal of A and of A^2 determines every opposed-edge product on the
actual tree. This holds for arbitrary real supported matrices, even at zeros. -/
theorem tree_punctured_moments_determine_products {n : ℕ} (t : OrderedTree n)
    (A B : TreeMatrix n) (hA : HasTreeMatrixSupport t A) (hB : HasTreeMatrixSupport t B)
    (h1 : ∀ i, A i i=B i i) (h2 : ∀ e : Fin n, (A*A) e.succ e.succ=(B*B) e.succ e.succ) :
    ∀ i j, A i j*A j i=B i j*B j i := by
  let M : TreeMatrix n := fun i j => A i j*A j i-B i j*B j i
  have hm : M=0 := tree_symmetric_zero_nonroot_row_sums t M
    (fun i j => by dsimp [M]; ring)
    (fun i => by dsimp [M]; rw [h1 i]; ring)
    (by
      intro i j hij hn
      dsimp [M]
      rw [hA i j hij hn,hB i j hij hn]
      ring)
    (by
      intro e
      simp only [M,Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h2 e))
  intro i j
  apply sub_eq_zero.mp
  exact congrArg (fun Q : TreeMatrix n => Q i j) hm

/-- Conservative tree rates are globally recovered from actual diagonal sums
and opposed-edge products whenever the reference inward rates are nonzero.
The competitor is unrestricted and the root leak can be zero or signed. -/
theorem rateChart_fiber_unique_nonzero_inward {n : ℕ} (t : OrderedTree n)
    (x y : TreeRates n) (ha : ∀ e : Fin n, x.1 e.succ ≠ 0)
    (h : rateChart t x=rateChart t y) : x=y := by
  have hd : ∀ v, x.1 v+parentCLM t x.2 v=y.1 v+parentCLM t y.2 v :=
    fun v => congrArg (fun z : TreeRates n => z.1 v) h
  have hc : ∀ e : Fin n, x.1 e.succ*x.2 e=y.1 e.succ*y.2 e :=
    fun e => congrArg (fun z : TreeRates n => z.2 e) h
  have he : ∀ e : Fin n, x.1 e.succ=y.1 e.succ ∧ x.2 e=y.2 e := by
    intro e
    induction e using (measure (fun e : Fin n => n-e.val)).wf.induction with
    | h e ih =>
      have hp : parentCLM t x.2 e.succ=parentCLM t y.2 e.succ := by
        rw [parentCLM_apply,parentCLM_apply]
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : t.parent f=e.succ
        · rw [if_pos hf,if_pos hf]
          have hlt : n-f.val<n-e.val := by
            have hle := t.parent_le f
            rw [hf] at hle
            have hfv := f.isLt
            have hev := e.isLt
            simp only [Fin.val_succ] at hle
            omega
          exact (ih f hlt).2
        · rw [if_neg hf,if_neg hf]
      have hv := hd e.succ
      rw [hp] at hv
      have haa : x.1 e.succ=y.1 e.succ := add_right_cancel hv
      have hee := hc e
      rw [← haa] at hee
      exact ⟨haa,mul_left_cancel₀ (ha e) hee⟩
  have hf : x.2=y.2 := funext (fun e => (he e).2)
  have hv : x.1=y.1 := by
    funext v
    have hh := hd v
    rw [hf] at hh
    exact add_right_cancel hh
  exact Prod.ext hv hf

/-- Exact global identifiability from just the first two diagonal moments of
all compartments. No genericity or full-response target is required. -/
theorem physical_two_diagonal_moments_identify {n : ℕ} (t : OrderedTree n)
    (x y : TreeRates n) (ha : ∀ e : Fin n, x.1 e.succ ≠ 0)
    (h1 : ∀ i, compartmentMatrix t x i i=compartmentMatrix t y i i)
    (h2 : ∀ i, (compartmentMatrix t x*compartmentMatrix t x) i i=
      (compartmentMatrix t y*compartmentMatrix t y) i i) : x=y := by
  have hs (z : TreeRates n) : HasTreeMatrixSupport t (compartmentMatrix t z) := by
    intro i j hij hn
    rw [compartment_offdiag_parent_formula _ _ _ _ hij]
    have hh := not_or.mp (mt (orderedGraph_adj_parent_iff _ _ _).mpr hn)
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp_all
  have hp := tree_punctured_moments_determine_products t _ _ (hs x) (hs y) h1 (fun e => h2 e.succ)
  apply rateChart_fiber_unique_nonzero_inward t x y ha
  apply Prod.ext
  · funext v
    exact neg_injective (by simpa only [compartment_diagonal] using h1 v)
  · funext e
    simpa only [rateChart,compartment_inward_entry,compartment_outward_entry] using hp (t.parent e) e.succ

end HydrologyTree
