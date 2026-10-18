#!/usr/bin/env python3
"""Independent snapshot precheck; never creates final source binding or PASS.
Run --replay to add a limited positive trust-zero replay and four same-type
controls for explicitly listed mature endpoints. All evidence goes to D.
"""
from pathlib import Path
import argparse,datetime,fcntl,json,os,re,signal,subprocess,sys,time
import reproduce as audit

SELECTED=[
  "ExtractionLOCC.Instrument.ofCP_outcomeMap",
  "ExtractionLOCC.Tree.channel_aliceInstrument",
  "ExtractionLOCC.IsClosureLOCC.exists_actual_protocol",
  "ExtractionRains.rainsEffect_iff_actual_protocol_effect",
  "OperationalCompletion.protocol_fidelity_one",
  "OperationalCompletion.finiteLOCC_capacities",
  "OperationalCompletion.measurable_physical_ensemble_bound",
  "OperationalCompletion.reservedFixedErrorTarget_gaussian",
  "OperationalCompletion.reserved_optimal_gaussian_limit",
  "OperationalCompletion.triangular_reserved_gaussian_shrinking_variance",
  "ExtractionSchur.flatHaarAverage_general_purity_scaled_limit",
  "CircuitRecursion.readoutCoordinates_physical",
  "CircuitRecursion.extractionOutput_purePower",
  "CircuitRecursion.bellPairYield_cPPT_maximal",
  "CircuitRecursion.extractionCircuit_isBigO",
  "CircuitRecursion.finiteLibrary_extraction",
]
DEFINITIONS=[
  "ExtractionLOCC.Tree","ExtractionLOCC.Instrument",
  "ExtractionLOCC.IsClosureLOCC","ExtractionRains.channel",
  "OperationalCompletion.reservedProtocol",
  "OperationalCompletion.reservedTargets",
  "OperationalCompletion.faithfulAttainableRates",
  "OperationalCompletion.exactAttainableRates",
  "OperationalCompletion.faithfulCapacity",
  "OperationalCompletion.exactCapacity",
  "CircuitRecursion.extractionCircuit","CircuitRecursion.extractionOutput",
  "CircuitRecursion.usesFiniteLibrary",
]
CONTROLS=[
  "ExtractionLOCC.Tree.channel_aliceInstrument",
  "ExtractionRains.rainsEffect_iff_actual_protocol_effect",
  "OperationalCompletion.triangular_reserved_gaussian_shrinking_variance",
  "CircuitRecursion.finiteLibrary_extraction",
]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--replay",action="store_true")
    args=ap.parse_args()
    s,roots,defs,controls=audit.scope_lists()
    assert set(SELECTED)<=set(roots) and set(DEFINITIONS)<=set(defs) and set(CONTROLS)<=set(controls)
    audit.check_execution_inputs()
    sys.path.insert(0,"/mnt/d/math/tmp/extraction-full-lean-20261016")
    from ensure_d_storage import configure_env
    env=configure_env(dict(os.environ))
    env["PATH"]="/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:"+env.get("PATH","")
    audit.check_pins()
    protected=audit.old_inventory()
    inputs=audit.inventory()
    for name in inputs:
        if name.startswith(audit.ROOT.relative_to(audit.REPO).as_posix()+"/"):continue
        exact=subprocess.check_output(["git","show",s["source_head"]+":"+name],cwd=audit.REPO)
        if exact!=(audit.REPO/name).read_bytes():raise RuntimeError("Snapshot source mismatch "+name)
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    out=Path("/mnt/d/math/tmp/extraction-resume-20261018/review-20261019")/("snapshot-precheck-"+stamp)
    out.mkdir(parents=True)
    audit.dump(out/"SNAPSHOT_INPUTS.json",dict(source_head=s["source_head"],files=inputs,protected_old_inputs=protected))
    audit.dump(out/"SCOPE.json",s)
    audit.dump(out/"EXECUTION.json",dict(execution_inputs=audit.readj(audit.ROOT/"EXECUTION_INPUTS.json"),python=sys.version,guard="D_BACKED_STORAGE_VERIFIED"))
    records=[]
    def stage(label,command,timeout):
        start=time.monotonic();log=out/(label+".log")
        with log.open("w") as f:
            process=subprocess.Popen(command,cwd=audit.ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL);process.wait();code=124
        rec=dict(stage=label,command=command,exit_code=code,seconds=round(time.monotonic()-start,3),log=log.name,sha256=audit.sha(log))
        records.append(rec);audit.dump(out/"STAGES.json",records)
        print(json.dumps(rec),flush=True)
        if code:raise RuntimeError("Stage failed "+label+"; "+str(log))
        return log.read_text()
    with open("/mnt/lean-research-d/tmp/extraction-shared-build.lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        stage("ordinary-build",["lake","build","CompletionAudit","CompletionVerification"],3600)
        kindlog=stage("planned-kind-types-axioms",["lake","env","lean","-j1","-M10000","Check.lean"],1200)
        if kindlog.count("DECLARATION_KIND_CHECK_PASS")!=1:raise RuntimeError("Kind marker missing")
        audit.dump(out/"PLANNED_AXIOM_REPORT.json",audit.parse_axiom_report(kindlog,roots+defs))
        replayed=False;closure_count=None;axioms=set()
        if args.replay:
            test=out/"SnapshotReplay.lean"
            stem=str(out/"snapshot-kernel")
            text="import CompletionAudit\nimport CompletionVerification.ReplaySupport\n\nrun_cmd (CompletionVerification.replayAll [\n"+",\n".join("  ``"+n for n in SELECTED+DEFINITIONS)+"\n] "+json.dumps(stem)+")\n\n"
            for i,n in enumerate(CONTROLS):text+="run_cmd CompletionVerification.rejectCorruptTheorem ``"+n+" "+json.dumps(str(out/("snapshot-control-"+str(i+1))))+"\n"
            test.write_text(text)
            replaylog=stage("limited-trust0-replay",["lake","env","lean","-j1","-M11000",str(test)],2400)
            if replaylog.count("EMPTY_KERNEL_REPLAY_PASS")!=1 or replaylog.count("CORRUPTED_PROOF_REJECTED")!=len(CONTROLS) or replaylog.count("TYPE_CLOSURE_REPLAY_PASS")!=len(CONTROLS) or replaylog.count("CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED")!=len(CONTROLS):raise RuntimeError("Missing limited replay/control markers")
            axioms=set((out/"snapshot-kernel-axioms.txt").read_text().splitlines())
            if not axioms<=audit.ALLOW:raise RuntimeError("Unexpected limited replay axiom")
            closure_count=int(re.search(r"EMPTY_KERNEL_REPLAY_PASS (\d+) declarations",replaylog).group(1))
            replayed=True
        if inputs!=audit.inventory() or protected!=audit.old_inventory():raise RuntimeError("Input drift during precheck")
        audit.check_pins();audit.check_execution_inputs()
        audit.dump(out/"SUMMARY.json",dict(status="LIMITED_SNAPSHOT_PRECHECK_ONLY",source_head=s["source_head"],full_final_audit=False,whole_manuscript_formalized=False,planned_theorem_types=len(roots),planned_model_definitions=len(defs),limited_replay=replayed,kernel_trust=0 if replayed else None,kernel_declarations=closure_count,axioms=sorted(axioms),snapshot_inputs_sha256=audit.sha(out/"SNAPSHOT_INPUTS.json"),replayed_theorems=SELECTED if replayed else [],replayed_definitions=DEFINITIONS if replayed else [],same_type_controls=CONTROLS if replayed else [],stages=records))
        print("LIMITED_SNAPSHOT_PRECHECK_ONLY "+str(out),flush=True)

if __name__=="__main__":main()
