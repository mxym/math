import SpectralProtocol.EnvelopeLower
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Tuple.Sort

open scoped BigOperators
namespace SpectralProtocol

/-- The finite harmonic factor with indices matched to ordered spectral prefixes. -/
noncomputable def harmonicFactor (N : ℕ) : ℝ := ∑ i : Fin N, (1:ℝ)/(i.val+1)

theorem antitone_entry_le_prefix_average {N : ℕ} (p : Fin N → ℝ)
    (hp : Antitone p) (i : Fin N) :
    p i  ≤  (∑ j : Fin (i.val+1), p (Fin.castLE (by omega) j))/(i.val+1) := by
  have hsum : ∑ j : Fin (i.val+1), p i  ≤ 
      ∑ j : Fin (i.val+1), p (Fin.castLE (by omega) j) := by
    apply Finset.sum_le_sum
    intro j _
    apply hp
    change j.val  ≤  i.val
    omega
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  push_cast at hsum
  exact (le_div_iff₀ (by positivity : (0:ℝ) < i.val+1)).mpr (by nlinarith [hsum])

/-- Once the actual effect entries are sorted, a quadratic budget bounds each
prefix entry. No independently assumed eigenvalue bound is needed. -/
theorem antitone_entry_sq_budget {N : ℕ} (z : Fin N → ℝ)
    (hz : ∀ i,0 ≤ z i) (hmono : Antitone z) (B : ℝ)
    (hbudget : ∑ i,z i^2 ≤ B) (i : Fin N) :
    (i.val+1:ℝ)*(z i)^2 ≤ B := by
  have hprefix : (i.val+1:ℝ)*(z i)^2  ≤ 
      ∑ j : Fin (i.val+1),z (Fin.castLE (by omega) j)^2 := by
    calc
      _ = ∑ j : Fin (i.val+1),(z i)^2 := by simp
      _  ≤  _ := by
        apply Finset.sum_le_sum
        intro j _
        have hj : z i  ≤  z (Fin.castLE (by omega) j) := hmono (by change j.val ≤ i.val;omega)
        nlinarith [hz i,hz (Fin.castLE (by omega) j)]
  have hs : (∑ j : Fin (i.val+1),z (Fin.castLE (by omega) j)^2)  ≤  ∑ j : Fin N,z j^2 := by
    let f : Fin (i.val+1) ↪ Fin N := Fin.castLEEmb (by omega)
    have h : (∑ j ∈ Finset.univ.map f,z j^2) ≤ ∑ j : Fin N,z j^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg (z j))
    simpa only [Finset.sum_map,f,Fin.coe_castLEEmb] using h
  exact hprefix.trans (hs.trans hbudget)

/-- Generic harmonic-prefix comparison; the finite rearrangement is internal. -/
theorem harmonic_prefix_comparison {N : ℕ} (p z v : Fin N → ℝ) (T : ℝ)
    (hp : Antitone p) (hp0 : ∀ i,0 ≤ p i)
    (hv : ∀ i,0 ≤ v i)
    (hprefix : ∀ i,v i*(∑ j : Fin (i.val+1),p (Fin.castLE (by omega) j)) ≤ T)
    (hordered : ∀ i,z (Tuple.sort (fun j => -z j) i) ≤ v i) :
    (∑ i,p i*z i) ≤ harmonicFactor N*T := by
  let σ := Tuple.sort (fun j => -z j)
  let zz := fun i => z (σ i)
  have hzz : Antitone zz := by
    intro i j hij
    have h := Tuple.monotone_sort (fun j => -z j) hij
    change -z (σ i) ≤  -z (σ j) at h
    change z (σ j) ≤ z (σ i)
    linarith
  have hmono : Monovary p zz := hp.monovary hzz
  have hrearr := hmono.sum_mul_comp_perm_le_sum_mul (σ := σ.symm)
  have hrearr' : (∑ i,p i*z i) ≤ ∑ i,p i*zz i := by
    simpa only [zz,Equiv.apply_symm_apply] using hrearr
  calc
    _  ≤  ∑ i,p i*zz i := hrearr'
    _  ≤  ∑ i : Fin N,T/(i.val+1) := by
      apply Finset.sum_le_sum
      intro i _
      have hpi := antitone_entry_le_prefix_average p hp i
      have hzv : zz i ≤ v i := hordered i
      calc
        p i*zz i ≤ p i*v i := mul_le_mul_of_nonneg_left hzv (hp0 i)
        _  ≤  ((∑ j : Fin (i.val+1),p (Fin.castLE (by omega) j))/(i.val+1))*v i :=
          mul_le_mul_of_nonneg_right hpi (hv i)
        _ = (v i*(∑ j : Fin (i.val+1),p (Fin.castLE (by omega) j)))/(i.val+1) := by ring
        _  ≤  _ := div_le_div_of_nonneg_right (hprefix i) (by positivity)
    _ = harmonicFactor N*T := by simp only [harmonicFactor,Finset.sum_mul];apply Finset.sum_congr rfl;intro i _;ring

end SpectralProtocol