import Spectrum.Tensor
import Mathlib.Data.Finset.Sort

open scoped BigOperators Classical

namespace ExtractionSpectrum

/-- Increasing finite enumerations cannot place the jth entry below j. -/
theorem strictMono_fin_nat_index_le {r : ℕ} (f : Fin r → ℕ)
    (hf : StrictMono f) (i : Fin r) : i.val ≤ f i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    induction i using Fin.cases with
    | zero => exact Nat.zero_le _
    | succ i =>
      have hprev := ih (fun j => f j.castSucc) (hf.comp Fin.strictMono_castSucc) i
      have hstep := hf (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hprev hstep)

/-- For a decreasing finite spectrum, the largest r entries dominate every
actual subset with r elements. No positivity assumption is needed. -/
theorem antitone_subset_sum_le_prefix {n r : ℕ} (p : Fin n → ℝ) (hp : Antitone p)
    (A : Finset (Fin n)) (hA : A.card = r) (hr : r ≤ n) :
    (∑ i ∈ A, p i) ≤ ∑ j : Fin r, p (Fin.castLE hr j) := by
  let e := A.orderEmbOfFin hA
  have he : (∑ i ∈ A, p i) = ∑ j : Fin r, p (e j) := by
    rw [← A.map_orderEmbOfFin_univ hA, Finset.sum_map]
    rfl
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  apply hp
  change j.val ≤ (e j).val
  exact strictMono_fin_nat_index_le (fun j => (e j).val)
    (Fin.val_strictMono.comp e.strictMono) j

end ExtractionSpectrum
