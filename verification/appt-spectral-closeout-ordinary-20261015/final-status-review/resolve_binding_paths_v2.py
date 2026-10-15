"""Preserve the exact v1, record its real metadata FAIL, and install corrected v2."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys
from review_helpers import sha,exact_hash
out=Path(__file__).resolve().parent;stage=out.with_name('spectral-closeout-publication')
public=stage/'public-sources';root=Path('/home/mxym/math-appt-multiscale-20261013')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def bind(p):
    b=p.read_bytes();return {'path':str(p.relative_to(out)),'bytes':len(b),'sha256':sha(b)}
v1=out/'superseded-v1-final-binding';assert not v1.exists();v1.mkdir()
names=['FINAL_STATUS_REVIEW.md','FINAL_STATUS_REVIEW.json','FINAL_STATUS_BINDING.json','METADATA_REVIEW_MANIFEST.json','INSTALLATION_RECEIPT.json','READING_LEDGER.json','RUN_LEDGER.json']
for name in names:(v1/name).write_bytes((out/name).read_bytes())
v1hash=sha((v1/'FINAL_STATUS_BINDING.json').read_bytes())
assert v1hash=='9a4690222f4e8c05c0b87009ae16b4aa40b59b2a0db8fc1a1f387565c9862c30'
for row in json.loads((v1/'METADATA_REVIEW_MANIFEST.json').read_bytes())['files']:
    if row['path'] in names:exact_hash((v1/row['path']).read_bytes(),row)
(v1/'PRESERVATION.json').write_text(json.dumps({'utc':now,'status':'SUPERSEDED_REVIEWER_METADATA_V1_PRESERVED','reason':'Reviewer-generated final binding lacks explicit repository path base; mathematical reports and all 383 candidate inputs unaffected','files':[bind(v1/n) for n in names],'original_binding_sha256':v1hash},indent=2)+'\n')
run=out/'binding-path-validation';run.mkdir()
checker=out/'validate_repository_path_binding.py'
failed=subprocess.run([sys.executable,str(checker),str(v1/'FINAL_STATUS_BINDING.json')],capture_output=True)
(run/'v1.stdout.txt').write_bytes(failed.stdout);(run/'v1.stderr.txt').write_bytes(failed.stderr)
assert failed.returncode==1 and b'AssertionError' in failed.stderr
finding={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FAIL','finding_kind':'Actual reviewer-generated metadata path-base validation failure; not an author/source mathematical finding','binding_v1_sha256':v1hash,'checker_sha256':sha(checker.read_bytes()),'returncode':failed.returncode,'stdout':bind(run/'v1.stdout.txt'),'stderr':bind(run/'v1.stderr.txt'),'cause':'Ambiguous final-status-review/... path without explicit repository_root base in identical four-project copies','resolution':'v2 uses explicit repository_path and path_base=repository_root for both report and decision','candidate_or_original_math_source_changed':False,'resolved_by_v2':True}
(out/'FINAL_BINDING_V1_PATH_FINDING.json').write_text(json.dumps(finding,indent=2)+'\n')

report=(out/'FINAL_STATUS_REVIEW.md').read_text()
report=report.replace('Status: **PASS**. Decision:', 'Version: **v2**. The exact v1 report/binding and installation receipt are preserved under `superseded-v1-final-binding`; its reviewer-generated path-base issue and actual failed validation are recorded in FINAL_BINDING_V1_PATH_FINDING.json. No candidate or mathematical source was changed.\n\nStatus: **PASS**. Decision:',1)
report=report.replace('The same binding is authorized for the three research project roots', 'The v2 report and decision targets use explicit repository-relative paths under `verification/appt-spectral-closeout-ordinary-20261015/final-status-review/`, with `path_base=repository_root`, so identical copies have one unambiguous target from every project root. The same binding is authorized for the three research project roots',1)
report=report.replace('No unexpected final-metadata execution failure occurred.', 'No unexpected candidate-byte or mathematical execution failure occurred. A subsequent validation of the reviewer-generated v1 final binding did produce one real metadata failure: its report/decision paths lacked an explicit repository base. The original v1 artifacts, actual exit code 1 and AssertionError stderr are preserved; v2 supplies explicit repository-root targets and the same validator passes. This is a resolved reviewer metadata finding, separate from the eight planned wrong-variant tests and from every author mathematical result.',1)
(out/'FINAL_STATUS_REVIEW.md').write_text(report)
reads=json.loads((out/'READING_LEDGER.json').read_bytes())
reads['version']=2;reads['v1_path_finding']=bind(out/'FINAL_BINDING_V1_PATH_FINDING.json')
(out/'READING_LEDGER.json').write_text(json.dumps(reads,indent=2,ensure_ascii=False)+'\n')
runs=json.loads((out/'RUN_LEDGER.json').read_bytes())
runs['version']=2;runs['resolved_reviewer_metadata_failure_history']=[bind(out/'FINAL_BINDING_V1_PATH_FINDING.json')]
runs['unexpected_unresolved_metadata_failures']=[]
runs['note']='The v1 path failure is one real resolved reviewer metadata finding, not one of the eight planned metadata negative controls.'
(out/'RUN_LEDGER.json').write_text(json.dumps(runs,indent=2,ensure_ascii=False)+'\n')
decision=json.loads((out/'FINAL_STATUS_REVIEW.json').read_bytes())
decision.update({'version':2,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'current_status_authority':'New v2 FINAL_STATUS_BINDING.json for the exact unchanged candidate','resolved_reviewer_metadata_findings':[finding],'unexpected_unresolved_metadata_failures':[],'superseded_v1_binding_sha256':v1hash,'read_ledger':bind(out/'READING_LEDGER.json'),'run_ledger':bind(out/'RUN_LEDGER.json'),'report_md':bind(out/'FINAL_STATUS_REVIEW.md')})
decision['unexpected_metadata_failures']=[{'type':'Reviewer metadata path-base ambiguity','resolved':True,'evidence':bind(out/'FINAL_BINDING_V1_PATH_FINDING.json')}]
(out/'FINAL_STATUS_REVIEW.json').write_text(json.dumps(decision,indent=2,ensure_ascii=False)+'\n')
binding=json.loads((out/'FINAL_STATUS_BINDING.json').read_bytes())
prefix='verification/appt-spectral-closeout-ordinary-20261015/final-status-review/'
binding.update({'version':2,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'supersedes_reviewer_binding_v1_sha256':v1hash,'review_report':{'path_base':'repository_root','repository_path':prefix+'FINAL_STATUS_REVIEW.md','sha256':sha((out/'FINAL_STATUS_REVIEW.md').read_bytes())},'review_decision':{'path_base':'repository_root','repository_path':prefix+'FINAL_STATUS_REVIEW.json','sha256':sha((out/'FINAL_STATUS_REVIEW.json').read_bytes())},'resolved_reviewer_metadata_finding':{'repository_path':prefix+'FINAL_BINDING_V1_PATH_FINDING.json','sha256':sha((out/'FINAL_BINDING_V1_PATH_FINDING.json').read_bytes()),'kind':'v1 report/decision path base missing; exact v1 preserved, v2 unambiguous; no source/math change'}})
binding['authoritative_current_status']='PASS for the exact unchanged candidate under this v2 binding. Superseded v1 reviewer metadata and historical preparation pending fields are preserved historical records, not current decisions.'
data=(json.dumps(binding,indent=2,ensure_ascii=False)+'\n').encode()
(out/'FINAL_STATUS_BINDING.json').write_bytes(data)
passed=subprocess.run([sys.executable,str(checker),str(out/'FINAL_STATUS_BINDING.json')],capture_output=True)
(run/'v2.stdout.txt').write_bytes(passed.stdout);(run/'v2.stderr.txt').write_bytes(passed.stderr)
assert passed.returncode==0
(run/'RESULT.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_AFTER_RECORDED_V1_FAIL','checker':bind(checker),'v1':{'returncode':failed.returncode,'stderr':bind(run/'v1.stderr.txt'),'stdout':bind(run/'v1.stdout.txt')},'v2':{'returncode':passed.returncode,'stderr':bind(run/'v2.stderr.txt'),'stdout':bind(run/'v2.stdout.txt')},'planned_negative_controls_count_unchanged':8},indent=2)+'\n')
raw=(stage/'FINAL_CANDIDATE_INPUTS.json').read_bytes();assert sha(raw)=='8589b1bdff22dac67e0419b578bbfde7a3c0319fe63d63b1d62bd994d1779c66'
candidate=json.loads(raw)
for rel,row in candidate['files'].items():exact_hash((stage/candidate['stage_file_lookup'][rel]).read_bytes(),row)
installed=[]
for name,dest in candidate['projects'].items():
    target=public/name/'FINAL_STATUS_BINDING.json'
    assert target.read_bytes()==(v1/'FINAL_STATUS_BINDING.json').read_bytes()
    target.write_bytes(data);assert target.read_bytes()==data
    installed.append({'path':str(target),'repo_path':dest+'/FINAL_STATUS_BINDING.json','sha256':sha(data),'bytes':len(data)})
for rel,row in candidate['files'].items():exact_hash((stage/candidate['stage_file_lookup'][rel]).read_bytes(),row)
assert subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip()==candidate['source_base']
assert not subprocess.check_output(['git','-C',str(root),'status','--porcelain']).strip()
(out/'INSTALLATION_RECEIPT.json').write_text(json.dumps({'version':2,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','binding_sha256':sha(data),'binding_bytes':len(data),'exactly_four_allowed_public_additions':installed,'v1_installed_bytes_preserved_in_superseded_directory':True,'all_383_original_candidate_inputs_rechecked_unchanged':True,'all_seven_binding_links_closed':True,'repository_relative_report_and_decision_paths_validated':True,'main_unchanged':True,'no_other_stage_public_write':True,'live_jobs':[]},indent=2)+'\n')
rows=[]
for p in sorted(out.rglob('*')):
    if p.is_file() and p.relative_to(out).as_posix()!='METADATA_REVIEW_MANIFEST.json':
        item=bind(p);item['public_copy_excluded']='private-protection-evidence' in p.parts or '__pycache__' in p.parts or p.suffix=='.pyc'
        if item['public_copy_excluded']:item['reason']='Pure private operational protection/task snapshots or generated cache; originals preserved'
        rows.append(item)
manifest={'version':2,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','self_excluded':True,'files':rows,'private_omissions_explicit':True,'current_binding_sha256':sha(data),'superseded_v1_exact_bytes_preserved':True,'resolved_actual_metadata_failures':1,'unresolved_failures':0}
(out/'METADATA_REVIEW_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
for row in rows:exact_hash((out/row['path']).read_bytes(),row)
print(json.dumps({'version':2,'status':'PASS','candidate_unchanged':383,'v1_preserved':True,'actual_v1_validator_exitcode':failed.returncode,'actual_v2_validator_exitcode':passed.returncode,'report':bind(out/'FINAL_STATUS_REVIEW.md'),'decision':bind(out/'FINAL_STATUS_REVIEW.json'),'binding':bind(out/'FINAL_STATUS_BINDING.json'),'manifest':bind(out/'METADATA_REVIEW_MANIFEST.json'),'four_installed_identical':True,'main_unchanged':True,'stopped':True},indent=2))
