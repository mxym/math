import EffectiveEncoding.DescriptorSerialization
import EffectiveEncoding.ProviderTraceCore

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- A precise cons/append source model. The annotation is a ghost counter:
emit charges one cons; append charges the left-list cons copies and its nil
case. Counter arithmetic itself, Nat bit work and input construction are outside
this structural model. -/
structure FieldRun where
  fields : List ℕ
  steps : ℕ

def FieldRun.empty : FieldRun := ⟨[],1⟩
def FieldRun.emit (n : ℕ) (r : FieldRun) : FieldRun := ⟨n::r.fields,r.steps+1⟩
def FieldRun.append (a b : FieldRun) : FieldRun :=
  ⟨a.fields++b.fields,a.steps+b.steps+a.fields.length+1⟩

def countedAngleFields (a : AngleCode) : FieldRun :=
  let atom:=match a.atom with
    | .pi => FieldRun.emit 0 FieldRun.empty
    | .merge A B j => FieldRun.emit 1 (FieldRun.emit A (FieldRun.emit B (FieldRun.emit j FieldRun.empty)))
  atom.append (FieldRun.emit (if a.negative then 1 else 0) (FieldRun.emit a.halvings FieldRun.empty))

def countedSingleFields : SingleCode → FieldRun
  | .hadamard => FieldRun.emit 0 FieldRun.empty
  | .yBasis => FieldRun.emit 1 FieldRun.empty
  | .phase a b => FieldRun.emit 2 ((countedAngleFields a).append (countedAngleFields b))
  | .inverse u => FieldRun.emit 3 (countedSingleFields u)

def countedGateFields {n : ℕ} : GateCode n → FieldRun
  | .single i u => FieldRun.emit 0 (FieldRun.emit i.val (countedSingleFields u))
  | .cnot c t _ => FieldRun.emit 1 (FieldRun.emit c.val (FieldRun.emit t.val FieldRun.empty))

def countedWordFields {n : ℕ} : WordCode n → FieldRun
  | [] => FieldRun.empty
  | g::gs => (countedGateFields g).append (countedWordFields gs)

def countedProgramFields {n : ℕ} (w : WordCode n) : FieldRun :=
  FieldRun.emit w.length (countedWordFields w)


theorem countedAngleFields_erase (a : AngleCode) : (countedAngleFields a).fields=a.fields := by
  cases he : a.atom <;> simp [countedAngleFields,he,FieldRun.append,FieldRun.emit,FieldRun.empty,AngleCode.fields]

theorem countedSingleFields_erase (u : SingleCode) : (countedSingleFields u).fields=u.fields := by
  induction u with
  | hadamard => rfl
  | yBasis => rfl
  | phase a b => simp [countedSingleFields,FieldRun.emit,FieldRun.append,countedAngleFields_erase,SingleCode.fields]
  | inverse u ih => simp [countedSingleFields,FieldRun.emit,ih,SingleCode.fields]

theorem countedGateFields_erase {n : ℕ} (g : GateCode n) : (countedGateFields g).fields=g.fields := by
  cases g <;> simp [countedGateFields,FieldRun.emit,FieldRun.empty,countedSingleFields_erase,GateCode.fields]

theorem countedWordFields_erase {n : ℕ} (w : WordCode n) : (countedWordFields w).fields=wordFields w := by
  induction w with
  | nil => rfl
  | cons g gs ih => simp [countedWordFields,FieldRun.append,countedGateFields_erase,ih,wordFields]

theorem countedProgramFields_erase {n : ℕ} (w : WordCode n) :
    (countedProgramFields w).fields=programFields w := by
  simp [countedProgramFields,FieldRun.emit,countedWordFields_erase,programFields]


theorem countedAngleFields_steps (a : AngleCode) : (countedAngleFields a).steps≤13 := by
  cases he : a.atom <;> simp [countedAngleFields,he,FieldRun.append,FieldRun.emit,FieldRun.empty]

theorem countedSingleFields_steps (u : SingleCode) : (countedSingleFields u).steps≤34+u.inverseDepth := by
  induction u with
  | hadamard => simp [countedSingleFields,FieldRun.emit,FieldRun.empty,SingleCode.inverseDepth]
  | yBasis => simp [countedSingleFields,FieldRun.emit,FieldRun.empty,SingleCode.inverseDepth]
  | phase a b =>
    have ha:=countedAngleFields_steps a
    have hb:=countedAngleFields_steps b
    have hl:=a.fields_length
    simp only [countedSingleFields,FieldRun.emit,FieldRun.append,countedAngleFields_erase,SingleCode.inverseDepth]
    omega
  | inverse u ih =>
    simp only [countedSingleFields,FieldRun.emit,SingleCode.inverseDepth]
    omega

theorem countedGateFields_steps {n M H D : ℕ} (g : GateCode n) (h : g.Fits M H D) :
    (countedGateFields g).steps≤36+D := by
  cases g with
  | single i u =>
    have hs:=countedSingleFields_steps u
    have hd:=h.2
    simp only [countedGateFields,FieldRun.emit]
    omega
  | cnot c t hc => simp [countedGateFields,FieldRun.emit,FieldRun.empty];omega


theorem countedWordFields_steps {n M H D : ℕ} (w : WordCode n) (h : WordFits M H D w) :
    (countedWordFields w).steps≤w.length*(52+2*D)+1 := by
  induction w with
  | nil => simp [countedWordFields,FieldRun.empty]
  | cons g gs ih =>
    have hg:=h g (by simp)
    have hs:=countedGateFields_steps g hg
    have hl:=g.fields_length hg
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [countedWordFields,FieldRun.append,countedGateFields_erase,List.length_cons]
    nlinarith

theorem extractionCode_countedFields_roundtrip (k : ℕ) (xs : List ℕ) :
    parseProgramFields (originalWireCount k) ((countedProgramFields (extractionCode k)).fields++xs)=
      some (extractionCode k,xs) := by
  rw [countedProgramFields_erase]
  exact extractionCode_fields_roundtrip k xs


theorem extractionCode_countedFields_steps (k : ℕ) :
    (countedProgramFields (extractionCode k)).steps≤54*(extractionCode k).length+2 := by
  have h:=countedWordFields_steps (extractionCode k) (extractionCode_fits k)
  simp only [countedProgramFields,FieldRun.emit]
  omega


theorem extractionCode_countedFields_steps_polynomial (k : ℕ) :
    (countedProgramFields (extractionCode k)).steps≤54*actualGatePolynomial k+2 :=
  (extractionCode_countedFields_steps k).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 54 (extractionCode_length_polynomial k)) 2)

end EffectiveEncoding
