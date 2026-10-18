import EffectiveEncoding.DescriptorBounds
import CircuitNumerical.IntegerExpressionBudgets

open EffectiveEncoding CircuitRecursion

def report (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

-- Deliberately bounded output-only checks; no semantic matrix is evaluated.
def main : IO Unit := do
  report "FINITE_SYNTAX_BYTECODE_BEGIN"
  unless (extractionCode 0).isEmpty do throw (IO.userError "k=0 extraction code must be empty")
  report "GENERATED_ZERO_LENGTH_PASS"
  let n := (extractionCode 1).length
  report s!"GENERATED_ONE_LENGTH {n}"
  unless (occupations 2).all (fun ν => (EffectiveEncoding.decode 2 (EffectiveEncoding.compactEncoding 2 ν)) == some ν) do
    throw (IO.userError "explicit occupation encode/decode failed")
  report "FINITE_OCCUPATION_ROUNDTRIP_PASS"
  let toy : WordCode 2 := [.single 0 .hadamard, .cnot 0 1 (by decide)]
  let labels := compileLabelWord (m:=1) (fun _ => [0]) toy
  unless labels.length == 2 do throw (IO.userError "finite label substitution shape failed")
  report "FINITE_LABEL_SUBSTITUTION_PASS"
  let zeroAngle : AngleCode := ⟨.merge 0 0 0,false,0⟩
  for u in [SingleCode.hadamard,.yBasis,.phase zeroAngle zeroAngle,.inverse .yBasis] do
    let packet := u.quaternionOracle 0
    report s!"LOW_PRECISION_PROVIDER {packet.toList}"
  unless (IntegerScalar.ofInt 0).inv.value == 0 do throw (IO.userError "integer inverse zero failed")
  unless ((IntegerScalar.ofInt (-1)).root 0).value == 0 do throw (IO.userError "integer root clamp failed")
  let e : ScalarExpression := .sqrt (.add (.literal (1/3)) (.literal (2/3))) 0
  unless e.integerRun.value == e.eval do throw (IO.userError "integer AST evaluator mismatch")
  report "INTEGER_BACKEND_VALUE_PASS"
  report "FINITE_SYNTAX_BYTECODE_CHECK_PASS"
