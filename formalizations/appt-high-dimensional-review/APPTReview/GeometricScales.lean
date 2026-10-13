import APPTReview.LacunaryPurityLimit

open scoped BigOperators
namespace APPTReview

/-- A fixed finite hierarchy, with each successive scale divided by three. -/
noncomputable def geometricScales : ℕ → List ℝ
  | 0 => []
  | k+1 => (1/3)::(geometricScales k).map (fun d => d/3)

theorem geometricScales_range (k : ℕ) :
    ∀ d∈geometricScales k,0<d ∧ d≤1/3 := by
  induction k with
  | zero => simp [geometricScales]
  | succ k ih =>
    intro d hd
    simp only [geometricScales,List.mem_cons,List.mem_map] at hd
    rcases hd with rfl | ⟨x,hx,rfl⟩
    · norm_num
    · obtain ⟨h0,h1⟩ := ih x hx
      constructor <;> linarith

theorem geometricScales_lacunary (k : ℕ) : LacunaryScales (geometricScales k) := by
  refine ⟨fun d hd => (geometricScales_range k d hd).1,?_⟩
  induction k with
  | zero => simp [geometricScales]
  | succ k ih =>
    rw [geometricScales,List.pairwise_cons]
    constructor
    · intro d hd
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
      have hb := (geometricScales_range k x hx).2
      linarith
    · rw [List.pairwise_map]
      exact ih.imp (fun h => by linarith)

theorem geometricScales_pairwise_gt (k : ℕ) : (geometricScales k).Pairwise (fun x y => y<x) := by
  induction k with
  | zero => simp [geometricScales]
  | succ k ih =>
    rw [geometricScales,List.pairwise_cons]
    constructor
    · intro d hd
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
      have hb := (geometricScales_range k x hx).2
      linarith
    · rw [List.pairwise_map]
      exact ih.imp (fun h => by linarith)

theorem geometricScales_nodup (k : ℕ) : (geometricScales k).Nodup :=
  (geometricScales_pairwise_gt k).imp (fun h => ne_of_gt h)

theorem geometricScales_length (k : ℕ) : (geometricScales k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [geometricScales,ih]

theorem geometricScales_card (k : ℕ) : (geometricScales k).toFinset.card=k := by
  rw [List.toFinset_card_of_nodup (geometricScales_nodup k),geometricScales_length]

end APPTReview
