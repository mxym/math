import APPT.CoefficientMerge

/-! Exact sparse polynomial arithmetic. All evaluation laws are proved in Lean;
closed coefficient equalities are checked by the kernel, not native evaluation. -/
namespace APPT.SparsePolynomial

abbrev Monomial := List Nat
abbrev Poly := List (Monomial × Int)

def monomial (g : Nat → ℝ) : Monomial → ℝ
  | [] => 1
  | i :: m => g i * monomial g m

def eval (g : Nat → ℝ) : Poly → ℝ
  | [] => 0
  | (m,c) :: p => (c : ℝ) * monomial g m + eval g p

def insertVar (i : Nat) : Monomial → Monomial
  | [] => [i]
  | j :: m => if i ≤ j then i :: j :: m else j :: insertVar i m

theorem monomial_insertVar (g : Nat → ℝ) (i : Nat) (m : Monomial) :
    monomial g (insertVar i m) = g i * monomial g m := by
  induction m with
  | nil => simp [insertVar, monomial]
  | cons j m ih =>
    simp only [insertVar]
    split <;> simp [monomial, ih] <;> ring

def mulMonomial : Monomial → Monomial → Monomial
  | [], n => n
  | i :: m, n => insertVar i (mulMonomial m n)

theorem monomial_mulMonomial (g : Nat → ℝ) (m n : Monomial) :
    monomial g (mulMonomial m n) = monomial g m * monomial g n := by
  induction m with
  | nil => simp [mulMonomial, monomial]
  | cons i m ih => simp [mulMonomial, monomial_insertVar, monomial, ih, mul_assoc]

def before : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | i :: m, j :: n => if i < j then true else if j < i then false else before m n

theorem eval_append (g : Nat → ℝ) (p q : Poly) :
    eval g (p ++ q) = eval g p + eval g q := by
  induction p with
  | nil => simp [eval]
  | cons x p ih => rcases x with ⟨m,c⟩; simp [eval, ih, add_assoc]

def mergeAux : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | k+1, (m,c) :: p, (n,d) :: q =>
    if m = n then (m,c+d) :: mergeAux k p q
    else if before m n then (m,c) :: mergeAux k p ((n,d) :: q)
    else (n,d) :: mergeAux k ((m,c) :: p) q

theorem eval_mergeAux (g : Nat → ℝ) (k : Nat) (p q : Poly) :
    eval g (mergeAux k p q) = eval g p + eval g q := by
  induction k generalizing p q with
  | zero => exact eval_append g p q
  | succ k ih =>
    cases p with
    | nil => simp [mergeAux, eval]
    | cons x p =>
      cases q with
      | nil => simp [mergeAux, eval]
      | cons y q =>
        rcases x with ⟨m,c⟩
        rcases y with ⟨n,d⟩
        by_cases he : m = n
        · subst n
          simp [mergeAux, eval, ih, Int.cast_add]; ring
        · by_cases hb : before m n = true
          · simp [mergeAux, he, hb, eval, ih]; ring
          · simp [mergeAux, he, hb, eval, ih]; ring

def merge (p q : Poly) : Poly := mergeAux (p.length + q.length) p q

theorem eval_merge (g : Nat → ℝ) (p q : Poly) :
    eval g (merge p q) = eval g p + eval g q := eval_mergeAux ..

def scale (c : Int) (p : Poly) : Poly := p.map (fun t => (t.1, c*t.2))

theorem eval_scale (g : Nat → ℝ) (c : Int) (p : Poly) :
    eval g (scale c p) = (c : ℝ)*eval g p := by
  induction p with
  | nil => simp [scale, eval]
  | cons t p ih =>
    rcases t with ⟨m,d⟩
    simp only [scale, List.map_cons, eval, Int.cast_mul] at *
    rw [ih]; ring

def times (m : Monomial) (c : Int) (p : Poly) : Poly :=
  p.map (fun t => (mulMonomial m t.1, c*t.2))

theorem eval_times (g : Nat → ℝ) (m : Monomial) (c : Int) (p : Poly) :
    eval g (times m c p) = (c : ℝ)*monomial g m*eval g p := by
  induction p with
  | nil => simp [times, eval]
  | cons t p ih =>
    rcases t with ⟨n,d⟩
    simp only [times, List.map_cons, eval, Int.cast_mul, monomial_mulMonomial] at *
    rw [ih]; ring

def mul : Poly → Poly → Poly
  | [], _ => []
  | (m,c) :: p, q => merge (times m c q) (mul p q)

theorem eval_mul (g : Nat → ℝ) (p q : Poly) :
    eval g (mul p q) = eval g p*eval g q := by
  induction p with
  | nil => simp [mul, eval]
  | cons t p ih =>
    rcases t with ⟨m,c⟩
    simp only [mul, eval_merge, eval_times, ih, eval]
    ring

def clean (p : Poly) : Poly := p.filter (fun t => t.2 != 0)

theorem eval_clean (g : Nat → ℝ) (p : Poly) : eval g (clean p) = eval g p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨m,c⟩
    by_cases hc : c = 0 <;> simp [clean, eval, hc] at * <;> exact ih

end APPT.SparsePolynomial
