import RawResourceAudit

open CircuitRecursion EffectiveEncoding

def main : IO Unit := do
  let a : IntegerScalar := ⟨9,4,by decide⟩
  let rooted := a.sharedBinaryRoot 2
  unless rooted.value.numerator == 6 && rooted.value.denominator == 4 && rooted.rootCharge > 0 do
    throw (IO.userError "shared binary root payload")
  let e : ScalarExpression := .sqrt (.literal (9/4)) 2
  let x := e.sharedCostedIntegerRun
  unless x.value.numerator == 6 && x.value.denominator == 4 && x.rootCharge == rooted.rootCharge do
    throw (IO.userError "shared expression root record")
  let packet : IntegerPacket := ⟨List.Vector.ofFn (fun i => if i.val == 0 then 3 else 0),2,by decide⟩
  let r := (rawPacketExpression packet).sharedCostedIntegerRun
  unless r.value.denominator == 16 && r.value.numerators.get 0 == 24 && r.rootCharge == 0 do
    throw (IO.userError "raw packet denominator packaging")
  let provided := SingleCode.rawPacketProgram .hadamard 0
  let cached := rawTargetProgramCache .hadamard 0
  unless provided.rootCharge != 0 && (cached.get 0).rootCharge == provided.rootCharge do
    throw (IO.userError "stored actual target-provider record")
  let atom : AngleAtom := .merge 1 1 1
  let merged := (atom.rawCosExpression 0).sharedCostedIntegerRun
  unless merged.value.numerator == 1 && merged.value.denominator == 2 && merged.rootCharge != 0 do
    throw (IO.userError "raw occupation-fraction provider")
  let fields := countedProgramFields (extractionCode 0)
  unless fields.fields == [0] && fields.steps == 2 do
    throw (IO.userError "empty descriptor serialization")
  let entry : Fin 1 → DyadicQuaternionOracle := fun _ _ => List.Vector.ofFn (fun _ => 0)
  let table : Fin 1 → List (Fin 1) := fun _ => []
  let w := chargedProviderExtractionCode entry (fun i => i) table 0 0 0
  unless w.isEmpty do
    throw (IO.userError "empty actual raw extraction code")
  IO.println "RAW_RESOURCE_SYNTAX_CHECK_PASS"
