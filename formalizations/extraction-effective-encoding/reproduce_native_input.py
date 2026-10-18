#!/usr/bin/env python3
"""Author actual-raw-integer-followup inventory/kind/type/axiom check, separate from independent replay."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys
PKG = Path(__file__).resolve().parent
TREE = PKG.parent.parent
PREFIX = "formalizations/extraction-effective-encoding"
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s[i:i+2]=="/-": depth+=1;i+=2
        elif depth and s[i:i+2]=="-/": depth-=1;i+=2
        elif depth:
            if s[i]=="\n":out.append("\n")
            i+=1
        elif s[i:i+2]=="--":
            j=s.find("\n",i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    assert depth==0
    return "".join(out)
def generate():
    rows=[];sources=[]
    pattern=re.compile(r"^(?:@\[[^\n]*\]\s*)?(?P<nc>noncomputable\s+)?"
        r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+"
        r"(?P<name>[A-Za-z_][A-Za-z0-9_.']*)",re.M)
    for p in [PKG/"EffectiveEncoding"/(name+".lean") for name in
            ["UnaryWordEncoding","NativeMergeInputs","PreparedNativeInputs"]]:
        if p.name=="Check.lean":continue
        raw=strip_comments(p.read_text())
        assert re.findall(r"^namespace\s+(\S+)",raw,re.M)==["EffectiveEncoding"],p
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b",raw),p
        decls=[]
        for m in pattern.finditer(raw):
            row=dict(name="EffectiveEncoding."+m["name"],kind=m["kind"],noncomputable=bool(m["nc"]),
                path=p.relative_to(TREE).as_posix(),line=raw[:m.start()].count("\n")+1)
            rows.append(row);decls.append(row["name"])
        sources.append(dict(path=p.relative_to(TREE).as_posix(),sha256=sha(p),declarations=decls))
    assert rows and len(rows)==len({r["name"] for r in rows})
    roots=[r["name"] for r in rows if r["kind"] in {"theorem","lemma"}]
    models=[r["name"] for r in rows if r["kind"] not in {"theorem","lemma"}]
    (PKG/"NATIVE_INPUT_ROOTS.txt").write_text("\n".join(roots)+"\n")
    (PKG/"NATIVE_INPUT_MODELS.txt").write_text("\n".join(models)+"\n")
    support='''import EffectiveEncoding.PreparedNativeInputs
import EffectiveEncoding.NativeInputEvaluation

open Lean Elab Command
namespace EffectiveEncodingNativeInputVerification

def checkKinds (theorems models : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for n in theorems do
    let some ci := env.find? n | throwError "Missing theorem {n}"
    unless ci.isTheorem do throwError "Expected theorem declaration {n}"
  for n in models do
    let some ci := env.find? n | throwError "Missing model {n}"
    match ci with
    | .defnInfo _ => pure ()
    | .inductInfo _ => pure ()
    | _ => throwError "Expected definition or inductive {n}"
  logInfo m!"OWNED_KIND_CHECK_PASS {theorems.length} theorems; {models.length} models"

end EffectiveEncodingNativeInputVerification

'''
    text=support+"run_cmd (EffectiveEncodingNativeInputVerification.checkKinds [\n"
    text+=",\n".join("  "+chr(96)*2+n for n in roots)+"\n] [\n"
    text+=",\n".join("  "+chr(96)*2+n for n in models)+"\n])\n\n"
    text+="".join("#check "+n+"\n#print axioms "+n+"\n" for n in roots+models)
    (PKG/"EffectiveEncoding/NativeInputCheck.lean").write_text(text)
    inventory=dict(status="GENERATED_AUTHOR_NATIVE_INPUT_SCOPE_NOT_INDEPENDENT_REPLAY",theorem_count=len(roots),
        model_count=len(models),declarations=rows,mathematical_sources=sources)
    (PKG/"NATIVE_INPUT_SOURCE_INVENTORY.json").write_text(json.dumps(inventory,indent=2)+"\n")
    print("GENERATED",len(roots),"THEOREMS",len(models),"MODELS",flush=True)
    return roots,models,inventory
def check():
    roots,models,inventory=generate()
    sys.path.insert(0,"/mnt/d/math/tmp/extraction-full-lean-20261016")
    from ensure_d_storage import configure_env
    env=configure_env(dict(os.environ))
    standard="--standard" in sys.argv
    if standard:
        cmd=["python3","/mnt/d/math/tmp/extraction-resume-20261018/worker_build.py",
            str(TREE),PREFIX,"EffectiveEncoding.NativeInputCheck"]
    else:
        cmd=["python3","/mnt/d/math/tmp/extraction-resume-20261018/lean_owned_check.py",
            str(TREE),PREFIX,"EffectiveEncoding.NativeInputCheck"]
    result=subprocess.run(cmd,cwd=TREE,env=env,text=True,capture_output=True)
    print(result.stdout,end="");print(result.stderr,end="",file=sys.stderr)
    assert result.returncode==0,"Serialized root check build failed"
    if standard:
        found=re.search(r"BUILD 0 LOG (\S+)",result.stdout);assert found
        log=Path(found[1])
    else:
        feedback=json.loads(result.stdout.splitlines()[0]);assert feedback["exit_code"]==0
        log=Path(feedback["log"])
    raw=log.read_text()
    raw=re.sub(r'^info:.*?:[0-9]+:[0-9]+: ','',raw,flags=re.M)
    assert f"OWNED_KIND_CHECK_PASS {len(roots)} theorems; {len(models)} models" in raw
    axioms={}
    for n,values in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",raw,re.M):
        assert n not in axioms
        axioms[n]=[a.strip() for a in values.split(",") if a.strip()]
    for n in re.findall(r"^'([^']+)' does not depend on any axioms$",raw,re.M):
        assert n not in axioms;axioms[n]=[]
    expected=set(roots+models)
    assert set(axioms)==expected,(expected-set(axioms),set(axioms)-expected)
    assert all(set(a)<=ALLOW for a in axioms.values()),"Unexpected axiom"
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    out=PKG/"verification"/("native-input-root-check-"+stamp);out.mkdir(parents=True)
    inputs={p.relative_to(TREE).as_posix():sha(p) for p in sorted((PKG/"EffectiveEncoding").glob("*.lean"))}
    for name in ["EffectiveEncoding.lean","lakefile.toml","lake-manifest.json","lean-toolchain",
            "NATIVE_INPUT_ROOTS.txt","NATIVE_INPUT_MODELS.txt","NATIVE_INPUT_SOURCE_INVENTORY.json","reproduce_native_input.py"]:
        inputs[(PKG/name).relative_to(TREE).as_posix()]=sha(PKG/name)
    head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=TREE,text=True).strip()
    report=dict(status=("AUTHOR_NATIVE_INPUT_STANDARD_ROOT_CHECK_PASS_NOT_INDEPENDENT_REPLAY" if standard else
        "AUTHOR_NATIVE_INPUT_ROOT_KIND_TYPE_AXIOM_CHECK_PASS_OWNED_ONLY_PENDING_AGGREGATE"),
        source_head=head,theorem_count=len(roots),model_count=len(models),log=str(log),
        log_sha256=sha(log),inputs=inputs,axioms=axioms,roots=roots,models=models)
    (out/"REPORT.json").write_text(json.dumps(report,indent=2)+"\n")
    print("AUTHOR_NATIVE_INPUT_ROOT_CHECK_PASS",len(roots),len(models),"REPORT",out/"REPORT.json",flush=True)
if __name__=="__main__":
    if "--generate" in sys.argv:generate()
    else:check()
