import OperationalCompletion.EntropyGrid
import MinimaxProfile.UniversalLimit

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

def gridSectorCount (k : ℕ) : ℕ := (k+1)^2

theorem gridSectorCount_pos (k : ℕ) : 0<gridSectorCount k := by
  unfold gridSectorCount
  positivity

def gridLocalDimension (m k : ℕ) : ℕ := m^k/gridSectorCount k

theorem gridLocalDimension_budget (m k : ℕ) :
    gridSectorCount k*gridLocalDimension m k≤m^k := by
  exact Nat.mul_div_le _ _

theorem gridLocalDimension_mono (m n k : ℕ) (hmn : m≤n) :
    gridLocalDimension m k ≤ gridLocalDimension n k := by
  exact Nat.div_le_div_right (Nat.pow_le_pow_left hmn k)

private theorem default_exists (a b K : ℕ) (hK : 0<K) :
    ∃ V : KrausPPTProtocol a b K,V.IsProductLocal := by
  obtain ⟨V,hLocal,_⟩ := projection_mass_protocol a b K hK 0 (by simp [Matrix.IsHermitian])
    (by simp) (by simp)
  exact ⟨V,hLocal⟩

def gridProtocol (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n) (hK : 0<K) :
    KrausPPTProtocol (m^k) (n^k) K :=
  if h : 0<k ∧ 0<gridLocalDimension m k then
    (geometric_universal_prefix_protocol m n k K (gridSectorCount k)
      (gridLocalDimension m k) (gridLocalDimension n k) hm hn h.1 hK h.2
      (gridLocalDimension_mono m n k hmn)
      (gridLocalDimension_budget m k) (gridLocalDimension_budget n k)).choose
  else (default_exists (m^k) (n^k) K hK).choose

theorem gridProtocol_isProductLocal (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) : (gridProtocol m n k K hm hn hmn hK).IsProductLocal := by
  unfold gridProtocol
  split
  next h =>
    exact (geometric_universal_prefix_protocol m n k K (gridSectorCount k)
      (gridLocalDimension m k) (gridLocalDimension n k) hm hn h.1 hK h.2
      (gridLocalDimension_mono m n k hmn)
      (gridLocalDimension_budget m k) (gridLocalDimension_budget n k)).choose_spec.1
  next h => exact (default_exists (m^k) (n^k) K hK).choose_spec

theorem gridProtocol_prefix (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (ha : 0<gridLocalDimension m k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (j : ℕ) (hj : j<gridSectorCount k) :
    ((gridWidth K (gridLocalDimension m k) j:ℝ)/K) *
      empiricalEntropyMass hX.1.isHermitian.eigenvalues k
        (sourceCutoff (m*n) k (gridLocalDimension m k) (gridLocalDimension n k)
          (gridWidth K (gridLocalDimension m k) j))
      ≤ (gridProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  unfold gridProtocol
  rw [dif_pos ⟨hk,ha⟩]
  exact (geometric_universal_prefix_protocol m n k K (gridSectorCount k)
    (gridLocalDimension m k) (gridLocalDimension n k) hm hn hk hK ha
    (gridLocalDimension_mono m n k hmn)
    (gridLocalDimension_budget m k) (gridLocalDimension_budget n k)).choose_spec.2 X hX j hj

theorem gridProtocol_first_mass (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (hKa : K≤gridLocalDimension m k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    empiricalEntropyMass hX.1.isHermitian.eigenvalues k
      (sourceCutoff (m*n) k (gridLocalDimension m k) (gridLocalDimension n k) K)
      ≤ (gridProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have ha : 0<gridLocalDimension m k := hK.trans_le hKa
  have h := gridProtocol_prefix m n k K hm hn hmn hK hk ha X hX 0 (gridSectorCount_pos k)
  have hd : gridWidth K (gridLocalDimension m k) 0=K := by
    simp [gridWidth,min_eq_left hKa,max_eq_right (show 1≤K by omega)]
  have hKR : (K:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hK)
  simpa only [hd,div_self hKR,one_mul] using h

end
end OperationalCompletion
