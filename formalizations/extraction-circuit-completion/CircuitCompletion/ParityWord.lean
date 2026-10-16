import CircuitCompletion.Reverse

open scoped BigOperators
open Matrix
namespace CircuitCompletion

abbrev Control {n : ℕ} (t : Fin n) := {c : Fin n // c≠t}

def cnotWord {n : ℕ} (t : Fin n) (cs : List (Control t)) : Circuit n :=
  cs.map (fun c => Gate.cnot c.1 t c.2)

def cnotWordEquiv {n : ℕ} (t : Fin n) : List (Control t) → Equiv.Perm (Bits n)
  | [] => Equiv.refl _
  | c::cs => (cnotEquiv c.1 t c.2).trans (cnotWordEquiv t cs)

def controlParity {n : ℕ} {t : Fin n} (cs : List (Control t)) (w : Bits n) : Bool :=
  (cs.map (fun c => w c.1)).foldr Bool.xor false

theorem controlParity_cnot {n : ℕ} (t : Fin n) (cs : List (Control t))
    (c : Control t) (w : Bits n) :
    controlParity cs (cnotFunction c.1 t w)=controlParity cs w := by
  unfold controlParity
  congr 1
  apply List.map_congr_left
  intro e he
  simp [cnotFunction,Function.update_of_ne e.2]

theorem cnotWordEquiv_apply_other {n : ℕ} (t : Fin n) (cs : List (Control t))
    (w : Bits n) (j : Fin n) (hj : j≠t) : cnotWordEquiv t cs w j=w j := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change cnotWordEquiv t cs (cnotFunction c.1 t w) j=w j
    rw [ih]
    simp [cnotFunction,hj]

theorem cnotWordEquiv_apply_target {n : ℕ} (t : Fin n) (cs : List (Control t))
    (w : Bits n) : cnotWordEquiv t cs w t=Bool.xor (w t) (controlParity cs w) := by
  induction cs generalizing w with
  | nil => simp [cnotWordEquiv,controlParity]
  | cons c cs ih =>
    change cnotWordEquiv t cs (cnotFunction c.1 t w) t=_
    rw [ih,controlParity_cnot]
    simp [cnotFunction,controlParity,Bool.xor_assoc]

theorem run_cnotWord {n : ℕ} (t : Fin n) (cs : List (Control t))
    (v : Bits n → ℂ) : run (cnotWord t cs) v=fun w => v ((cnotWordEquiv t cs).symm w) := by
  induction cs generalizing v with
  | nil => simp [cnotWord,run,denote,cnotWordEquiv]
  | cons c cs ih =>
    change run ([Gate.cnot c.1 t c.2]++cnotWord t cs) v=_
    rw [run_append,ih]
    simp only [run,denote,one_mul,cnot_action,cnotWordEquiv,Equiv.symm_trans_apply]
    rfl

/-- Compute parity into a participating original wire, apply one one-qubit
phase, and uncompute. The word uses exactly 2|cs|+1 primitive gates. -/
noncomputable def parityPhaseWord {n : ℕ} (t : Fin n) (cs : List (Control t))
    (z : Bool → ℂ) (hz : ∀ b,Complex.normSq (z b)=1) : Circuit n :=
  cnotWord t cs++[Gate.single t (diagonalUnitary z hz)]++reverseCircuit (cnotWord t cs)

theorem parityPhaseWord_action {n : ℕ} (t : Fin n) (cs : List (Control t))
    (z : Bool → ℂ) (hz : ∀ b,Complex.normSq (z b)=1) (v : Bits n → ℂ) :
    run (parityPhaseWord t cs z hz) v=
      fun w => z (Bool.xor (w t) (controlParity cs w))*v w := by
  let f : Bits n → ℂ := fun w => z (cnotWordEquiv t cs w t)*v w
  have hmid : run [Gate.single t (diagonalUnitary z hz)] (run (cnotWord t cs) v)=
      run (cnotWord t cs) f := by
    rw [run_cnotWord]
    have hsingle (u : Bits n → ℂ) :
        run [Gate.single t (diagonalUnitary z hz)] u=
          ((Gate.single t (diagonalUnitary z hz)).denote : Matrix (Bits n) (Bits n) ℂ)*ᵥu := by
      simp only [run,denote,one_mul]
    rw [hsingle,singleWire_diagonal_action,run_cnotWord]
    ext w
    simp [f]
  simp only [parityPhaseWord,run_append]
  rw [hmid,run_reverseCircuit]
  funext w
  simp [f,cnotWordEquiv_apply_target]

theorem parityPhaseWord_length {n : ℕ} (t : Fin n) (cs : List (Control t))
    (z : Bool → ℂ) (hz : ∀ b,Complex.normSq (z b)=1) :
    (parityPhaseWord t cs z hz).length=2*cs.length+1 := by
  simp [parityPhaseWord,reverseCircuit_length,cnotWord]
  omega

end CircuitCompletion
