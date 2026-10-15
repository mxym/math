import hashlib,json,pathlib,datetime,subprocess
out=pathlib.Path(__file__).resolve().parent
src=pathlib.Path('/home/mxym/math-breadth-tcs-20261015/research/breadth-tcs-20261015/phase-4-depth-appt')
sha=lambda b:hashlib.sha256(b).hexdigest()
names=['GLOBAL_MIXED_V1_MANIFEST.json','CRITICAL_V1_MANIFEST.json','critical_exact_intervals.py','CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','global_mixed_turn_certificate.py','GLOBAL_MIXED_TURN_CERTIFICATE.json','replay_critical_certificate.py','replay_global_turn_certificate.py','global_mixed_turn_algebra.py','GLOBAL_TURN_ALGEBRA_CONTROL.json','no_islands_author_controls.py','NO_ISLANDS_AUTHOR_CONTROL.json','GLOBAL_MIXED_AUTHOR_REPLAY.json','CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json','PURE_ENVELOPE_GE_ONE.md']
records=[]
for name in names:
    data=(src/name).read_bytes()
    dest=out/'frozen-dependencies'/name
    dest.parent.mkdir(exist_ok=True)
    assert not dest.exists()
    dest.write_bytes(data)
    records.append({'path':str(src/name),'copy':str(dest.relative_to(out)),'bytes':len(data),'sha256':sha(data)})
by={r['path']:r for r in records}
for name in ['GLOBAL_MIXED_V1_MANIFEST.json','CRITICAL_V1_MANIFEST.json']:
    m=json.loads((src/name).read_bytes())
    for row in m['files']+m['dependencies']:
        actual=(pathlib.Path(row['path'])).read_bytes()
        assert sha(actual)==row['sha256'],row['path']
        if 'bytes' in row:assert len(actual)==row['bytes']
        # Bind every listed file, but do not call optional discovery scientific proof.
        if row['path'] not in by:
            dest=out/'frozen-dependencies'/pathlib.Path(row['path']).name
            if dest.exists():assert dest.read_bytes()==actual
            else:dest.write_bytes(actual)
            record={'path':row['path'],'copy':str(dest.relative_to(out)),'bytes':len(actual),'sha256':sha(actual)}
            records.append(record);by[row['path']]=record
for p in (out/'frozen-author/credited-inputs/phase4').iterdir():
    assert p.read_bytes()==(src/p.name).read_bytes()
for row in json.loads((out/'frozen-author/AUTHOR_V1_MANIFEST.json').read_bytes())['files']:
    b=(out/'frozen-author'/row['path']).read_bytes()
    assert sha(b)==row['sha256'] and len(b)==row['bytes']
commit='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
for rel in ['research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md','research/appt-linear-critical-rigidity-20261015/PAPER.md']:
    b=subprocess.check_output(['git','-C','/home/mxym/math-appt-multiscale-20261013','show',commit+':'+rel])
    assert b==(out/'frozen-author/credited-inputs'/rel).read_bytes()
(out/'DEPENDENCY_BINDING.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_listed_manifest_hashes_checked':True,'L_and_S_exact_commit_checked':commit,'records':records},indent=2)+'\n')
run=out/'replay-work';run.mkdir()
for r in records:
    p=out/r['copy'];(run/p.name).write_bytes(p.read_bytes())
for p in (out/'frozen-author/credited-inputs/phase4').iterdir():(run/p.name).write_bytes(p.read_bytes())
print(json.dumps({'copied_and_bound_dependencies':len(records),'archive_manifest_rows_verified':13,'L_S_commit_verified':True}))
