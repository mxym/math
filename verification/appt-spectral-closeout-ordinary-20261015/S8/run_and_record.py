from pathlib import Path
import subprocess,json,hashlib,datetime,sys
out=Path(__file__).resolve().parent
logs=out/'logs';logs.mkdir(exist_ok=True)
programs=[out/'replay-work/replay_critical_certificate.py',out/'replay-work/replay_global_turn_certificate.py',out/'replay-work/global_mixed_turn_algebra.py',out/'replay-work/no_islands_author_controls.py',out/'independent_controls.py']
rows=[]
for program in programs:
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    result=subprocess.run([sys.executable,str(program)],capture_output=True,text=True)
    stem=program.stem
    stdout=logs/(stem+'.stdout.txt');stderr=logs/(stem+'.stderr.txt')
    stdout.write_text(result.stdout);stderr.write_text(result.stderr)
    rows.append({'program':str(program.relative_to(out)),'program_sha256':hashlib.sha256(program.read_bytes()).hexdigest(),'started_utc':now,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'returncode':result.returncode,'stdout':str(stdout.relative_to(out)),'stderr':str(stderr.relative_to(out))})
    print(json.dumps({'program':stem,'returncode':result.returncode}))
    if result.returncode:print(result.stderr)
(out/'RUN_LOG.json').write_text(json.dumps({'runs':rows,'all_pass':all(r['returncode']==0 for r in rows),'scope':'Private copied inputs only; no author-source execution in place'},indent=2)+'\n')
assert all(r['returncode']==0 for r in rows)

# Read and summarize the entire author control JSON, distinguishing discovery
# samples from exact proof. Every stored sample is checked for expected fields.
frozen=out/'frozen-dependencies/NO_ISLANDS_AUTHOR_CONTROL.json'
control=json.loads(frozen.read_bytes())
assert all(control['exact_rational_algebra_identities'].values())
for sample in control['finite_floating_checks']:
    assert all(k in sample for k in ['x','K','admissible_v','normalized_delta_log_derivative','H_log_derivative'])
    assert all(float(sample[k])>0 for k in ['admissible_v','normalized_delta_log_derivative','H_log_derivative'])
print(json.dumps({'frozen_author_control_full_json_read':True,'sample_count':len(control['finite_floating_checks']),'finite_samples_are_not_proof':True}))
