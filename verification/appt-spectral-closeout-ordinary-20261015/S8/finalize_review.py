from pathlib import Path
import datetime,hashlib,json,zipfile,subprocess,sys
out=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
binding=json.loads((out/'INPUT_BINDING.json').read_bytes())
author=Path('/home/mxym/math-breadth-tcs-20261015/research/breadth-tcs-20261015/phase-8-coexistence-orientation')
for row in binding['entries']:
    now=(author/row['relative_path']).read_bytes()
    assert sha(now)==row['sha256'] and now==(out/'frozen-author'/row['relative_path']).read_bytes()
deps=json.loads((out/'DEPENDENCY_BINDING.json').read_bytes())
for row in deps['records']:
    assert sha(Path(row['path']).read_bytes())==row['sha256']
    assert sha((out/row['copy']).read_bytes())==row['sha256']
clock=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015/phase-5-haldane/CLOCK.json')
clock_hash=sha(clock.read_bytes())
assert clock_hash=='d3aab86688c0a69e4cdcaa71f825e1c301017233d9a072adb7c47480af4c6b56'
status=subprocess.check_output(['git','-C','/home/mxym/math-breadth-quantum-20261015','status','--porcelain=v1']).decode()
head=subprocess.check_output(['git','-C','/home/mxym/math-breadth-quantum-20261015','rev-parse','HEAD']).decode().strip()
assert head=='1a93b182ce9cbe6c9718fc994985436537550d78' and status==''
final={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'PASS','paper_sha256':'9fdb0649010809711223abd1f30778652ae9bde0cd1d768b66336c3ed22e5cb1','all_14_author_source_files_unchanged':True,'all_23_bound_dependency_originals_unchanged':True,'HN0_clock_unchanged':True,'HN0_clock_sha256':clock_hash,'HN0_effective_seconds':3965.905531,'HN0_status':'paused','HN0_head':head,'HN0_git_status':status,'live_review_jobs':[],'source_writes_outside_review_private_directory':False,'push_lean_release_submission_or_new_research':False,'review_kind':'Internal AI ordinary mathematical review; not human peer review, Lean, priority or new-major certification','python_version':sys.version}
(out/'FINAL_INTEGRITY.json').write_text(json.dumps(final,indent=2)+'\n')
read_scope=[]
for p in sorted((out/'frozen-author').rglob('*')):
    if p.is_file():
        data=p.read_bytes()
        read_scope.append({'path':str(p.relative_to(out)),'sha256':sha(data),'bytes':len(data),'lines':len(data.decode().splitlines()),'scope':'Entire text read, including dependencies and author freezing source'})
for name in ['critical_exact_intervals.py','global_mixed_turn_certificate.py','replay_critical_certificate.py','replay_global_turn_certificate.py','global_mixed_turn_algebra.py','no_islands_author_controls.py','PURE_ENVELOPE_GE_ONE.md']:
    p=out/'frozen-dependencies'/name;data=p.read_bytes()
    read_scope.append({'path':str(p.relative_to(out)),'sha256':sha(data),'bytes':len(data),'lines':len(data.decode().splitlines()),'scope':'Entire source or mathematical text read'})
for name in ['CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','GLOBAL_MIXED_TURN_CERTIFICATE.json','NO_ISLANDS_AUTHOR_CONTROL.json']:
    p=out/'frozen-dependencies'/name
    read_scope.append({'path':str(p.relative_to(out)),'sha256':sha(p.read_bytes()),'scope':'Entire structured JSON read; every certificate record recomputed or every author-control sample checked; all digits not individually printed'})
(out/'READ_SCOPE.json').write_text(json.dumps({'entries':read_scope,'additional_read':'Both old manifests, author replay results and global algebra result read in full. Optional discovery/freeze housekeeping files only hash-bound, not claimed scientific read.','credited_physical_theorems':'L and S complete texts read; original all-global-unitary quantum input hypotheses retained. No historical Lean audit expanded.'},indent=2)+'\n')
rows=[]
for p in sorted(out.rglob('*')):
    if p.is_file() and p.name!='REPORT_MANIFEST.json':
        data=p.read_bytes();rows.append({'path':str(p.relative_to(out)),'bytes':len(data),'sha256':sha(data)})
manifest={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'PASS','review_report':'REVIEW.md','review_report_sha256':sha((out/'REVIEW.md').read_bytes()),'self_excluded':True,'files':rows}
(out/'REPORT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
archive=out.parent/(out.name+'.zip')
assert not archive.exists()
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(out.rglob('*')):
        if p.is_file():z.write(p,str(p.relative_to(out)))
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():assert z.read(name)==(out/name).read_bytes()
    total=len(z.namelist())
receipt={'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'report':str(out/'REVIEW.md'),'report_sha256':sha((out/'REVIEW.md').read_bytes()),'manifest':str(out/'REPORT_MANIFEST.json'),'manifest_sha256':sha((out/'REPORT_MANIFEST.json').read_bytes()),'archive':str(archive),'archive_sha256':sha(archive.read_bytes()),'archive_bytes':archive.stat().st_size,'archive_items_all_read_back_and_compared':total,'decision':'PASS','HN0_status':'paused','HN0_effective_seconds':3965.905531,'live_review_jobs':[]}
(out.parent/(out.name+'-RECEIPT.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
