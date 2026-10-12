#!/usr/bin/env python3
"""Cross-check the completed release-wrapper evidence without rebuilding caches."""
from pathlib import Path
import json,gzip,hashlib,re,collections
BASE=Path(__file__).resolve().parent.parent
ROOT=BASE/'final_copy/formalizations/continuum-remainder-avoidance'
OUT=BASE/'final_copy_verification'
AUDIT=BASE.parent/'lean_continuum_remainder_independent_audit_20261007'
def need(v,s):
 if not v:raise RuntimeError(s)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_text())
r=j(OUT/'VERIFICATION.json');need(r['status']=='PASS','wrapper not complete')
b=j(OUT/'BUILD.json');need(b['status']=='PASS' and len(b['owned_modules'])==65,'build count')
for n,sha in r['proof_source_hashes'].items():need(h(ROOT/n)==sha,'wrapper proof source differs '+n)
owned=j(OUT/'OWNED_OBJECT_SHA256.json');need(len(owned)==65,'owned artifact count')
for n,sha in owned.items():need(h(OUT/'owned'/Path(n.replace('.','/')).with_suffix('.olean'))==sha,'fresh artifact hash '+n)
for name in ['FAST_PROOF_GRAPH.json','FAST_OWNED_INVENTORY.json','FAST_CLOSURE_SUMMARY.json']:
 actual=json.loads(gzip.decompress((OUT/(name+'.gz')).read_bytes()))
 old=j(AUDIT/'evidence'/name)
 # JSON order is not part of declaration/graph identity.
 if isinstance(actual,list):
  key='name';need({x[key]:x for x in actual}=={x[key]:x for x in old},'historical data differs '+name)
 else:need(actual==old,'historical summary differs '+name)
module=j(OUT/'ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json');historical={x['module']:x for x in j(AUDIT/'evidence/ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json')}
need(len(module)==1322 and len(historical)==1322,'defining module count')
diffs=[]
for row in module:
 prev=historical[row['module']]
 need(row['source_relative']==prev['source_relative'] and row['source_sha256']==prev['source_sha256'],'source hash changed')
 if row['artifact_sha256']!=prev['artifact_sha256']:
  need(row['module'] in owned,'reused dependency artifact changed')
  diffs.append(row['module'])
need(len(diffs)==9,'unexpected artifact difference count')
for key,s in [('ReplayClosure','EMPTY_KERNEL_REPLAY_PASS 34923 declarations'),('ReplayAllSafeOwned','ALL_SAFE_OWNED_EMPTY_KERNEL_REPLAY_PASS 35620 declarations')]:
 t=(OUT/'logs'/(key+'.log')).read_text();need(s in t and 'trust level zero; empty kernel environment' in t and 'error:' not in t,'replay log')
need('Forbidden owned axiom GloballyNamedInjectedTarget' in (OUT/'logs/ownership-injection-rejection.log').read_text(),'ownership guard')
text=(OUT/'logs/AllPublicAxioms.log').read_text();rows=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
need(len(rows)==568 and len({n for n,_ in rows})==568,'axiom log count')
need(all(set(v.strip() for v in s.split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'} for _,s in rows),'unexpected axiom')
controls=j(OUT/'CONTROLS.json');need(len(controls)==66 and all(x['passed'] for x in controls),'control count')
logs=list((OUT/'logs').glob('negative.*.log'));need(len(logs)==34,'negative log count')
for p in logs:
 t=p.read_text();need('error:' in t and not any(x.lower() in t.lower() for x in ['unknown module','unexpected token','unknown constant','unknown identifier','failed to synthesize']),'infrastructure failure '+p.name)
 need(any(x in t for x in ['⊢ False','omega could not prove the goal','Tactic `decide` proved']),'missing intended mathematical rejection')
need((OUT/'logs/semantic-normal.log').read_bytes()==(OUT/'logs/semantic-optimized.log').read_bytes(),'arithmetic Python mode mismatch')
need(len(j(OUT/'logs/semantic-normal.log')['exact_arithmetic_regressions'])==15,'arithmetic count')
licenses=ROOT/'third_party_licenses';prior=BASE.parent/'geometric_avoidance_public_release_20261007/v2_clean_extraction/geometric-avoidance/third_party_licenses'
count=0
for p in licenses.rglob('*'):
 if p.is_file() and p.name!='SHA256SUMS':need(p.read_bytes()==(prior/p.relative_to(licenses)).read_bytes(),'license notice changed');count+=1
report={'status':'PASS','scope':'Independent evidence/source cross-check of the completed packaging-worker fresh-copy wrapper; not a second fresh Lean build or replay run by this reviewer','fresh_owned_artifacts_directly_hashed':65,'proof_sources_checked':len(r['proof_source_hashes']),'graph_inventory_and_summary_equal_to_independent_math_audit':True,'actual_defining_module_source_records_equal':1322,'reused_dependency_artifact_records_equal':True,'owned_object_identical_count':56,'owned_object_different_count':9,'endpoint_union_replay_log_declarations':34923,'all_safe_replay_log_declarations':35620,'public_axiom_log_rows':568,'intended_negative_control_logs_checked':34,'control_result_rows':66,'arithmetic_regressions_both_modes_equal':15,'retained_license_files_identical_to_prior_release':count,'reviewed_record_sha256':{n:h(OUT/n) for n in ['VERIFICATION.json','BUILD.json','DECLARATION_COMPARISON.json','ACTUAL_MODULE_COMPARISON.json','CONTROLS.json','PACKAGING_GUARD_CONTROLS.json','logs/ReplayClosure.log','logs/ReplayAllSafeOwned.log']}}
(Path(__file__).parent/'COMPLETED_WRAPPER_EVIDENCE_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='reviewed_record_sha256'},indent=2))
