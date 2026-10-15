from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-4-depth-appt'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-4-depth-appt')
now=dt.datetime.now(dt.timezone.utc)
tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert head=='bf8f132cad7b00e20f431b0b486a9b581240b9d7'
tracked=[x for x in subprocess.check_output(['git','-C',str(repo),'ls-files','-z','--',prefix]).decode().split('\0') if x]
papers=['LAST_MIXED_BOUNDARY.md','NO_ISLANDS.md','CRITICAL_UNIQUENESS_CERTIFICATE.md','GLOBAL_MIXED_PHASE.md']
engines=['critical_exact_intervals.py','global_mixed_turn_certificate.py']
certificates=['CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','GLOBAL_MIXED_TURN_CERTIFICATE.json']
replayers=['replay_critical_certificate.py','replay_global_turn_certificate.py']
frozen=[]
for name in tracked:
    p=repo/name
    assert p.read_bytes()==subprocess.check_output(['git','-C',str(repo),'show',head+':'+name]),name
    short=p.name
    if short in papers:role='new complete scientific author manuscript; independent full ordinary read pending'
    elif short in engines:role='exact integer interval source; independent mathematical/code read pending'
    elif short in certificates:role='complete covering certificate; every recorded leaf and partition is in review scope'
    elif short in replayers:role='full exact leaf and coverage replayer; author replay is not independent review'
    elif short=='PURE_ENVELOPE_GE_ONE.md':role='D1 support; separate ordinary-read completion reported by parent; no approval of four new scopes implied'
    elif '/credited-inputs/' in name:role='exact credited main scientific/source-map input, complete read in this role'
    elif 'DISCOVERY' in short or short.startswith('explore_'):role='floating discovery or exploratory control; excluded as proof of global claims'
    elif 'CONTROL' in short or 'REPLAY' in short:role='author-only auxiliary control/result, not an independent review'
    elif 'MANIFEST' in short or short=='CREDITED_SOURCES.json':role='existing frozen byte manifest or provenance; unchanged'
    else:role='historical scope/status/preservation helper; not a new mathematical dependency'
    frozen.append({'path':name,'bytes':p.stat().st_size,'sha256':sha(p),'role':role,'frozen_commit':head})

credited=json.loads((folder/'CREDITED_SOURCES.json').read_text())
primary=json.loads((folder/'PRIMARY_SCREEN.json').read_text())
source_inputs={
 'created_utc':now.isoformat(),'frozen_owner_commit':head,
 'scope':'Independent four-manuscript APPT scalar phase review plus its exact code/data; not old Lean or breadth stages',
 'root_source_capture_commit':credited['root_commit'],
 'new_scientific_manuscripts':papers,
 'credited_complete_read_inputs':credited['inputs'],
 'original_objects':'Complex PSD trace-one densities, PPT after every global unitary; 2<=m<=n,m->infinity,D=mn',
 'window':'alpha>1,alpha/m->c in (0,infinity),3^alpha/D->r in [0,infinity); arbitrary aspect ratios',
 'nearoptimality':'(log D-S_alpha(rho))/E_alpha->1 on first-nonzero scale',
 'retained_losses':['Distance of actual (L,theta) to FULL compact scalar argmax tends to zero','J->0','Pi_actual->0'],
 'retained_ties':'All pure/double/triple ties; redundant pole h line; alternation allowed; no forced one-phase selection at moving ties',
 'actual_transfer':'Credited S covers every actual APPT density and attains every scalar maximizer; W1 body law and peak domain l<2 retained',
 'external_primary_read_scope':primary['current_primary_pages'],
 'priority_scope':primary['limit'],
 'not_dependencies':['Root T/v1-v2 scalar drafts','Root lower-onset B7 draft','Fixed-m log-order main-line research',
  'New or repeated Lean audit','Floating-point candidate root or finite sampled absence','SC0,FEI,LR0 closed/interrupted stages'],
 'frozen_inputs':frozen,
 'author':{'name':'Yongxian Zhang (张永贤)','affiliation':'South China University of Technology',
           'email':'mxymmxym1@gmail.com','orcid':'0009-0000-3864-3536',
           'funding':'No external funding','ai_assistance':'OpenAI AI assistants assisted research and writing',
           'rights':'Original material all rights reserved; third-party notices and attribution retained'},
 'review_status':'Four new scopes author-only, ordinary independent full read and final metadata binding pending',
 'no_new_major_count':True,'no_new_lean_coverage':True,'no_external_submission':True}
dump(folder/'SOURCE_INPUTS.json',source_inputs)

scope={
 'created_utc':now.isoformat(),'owner_commit_before_metadata':head,
 'reading_order':papers,'scope_status':'Author complete, independent full ordinary review pending',
 'D1_support_status':'Parent reported separate ordinary-read completion; exact final publication/index binding remains parent-owned',
 'independent_review_scope':['Every analytic proof and dependency bridge','Complete original L/S matrix quantifiers and alpha domain',
  'Every scalar endpoint and every tie','All loss conditions and actual attainability',
  'Both exact integer engines and elementary/normalized series remainder proofs',
  'All 73 critical leaves and partitions','All 74 global leaves and full rational 2D partitions',
  'K=0 removable charts and seven explicit K-cap exclusions','Hessian and analytic coexistence arguments',
  'Final exact metadata binding in a separate step'],
 'excluded_review_scope':['No Lean roots, tools, trust audit or CI enlargement','No re-audit of credited entire main proofs',
  'No external human peer review or priority certification','No major-problem tally increment'],
 'reviewer_reproduction':'Private scratch only; standard-library full replayers, originals unchanged',
 'status_index_policy':'Do not label independently proved until actual review and final exact metadata binding pass',
 'revisions_policy':'Preserve all v1 bytes and any actual FAIL; revised proof/code/data must use a new explicit version and renewed review',
 'known_limits':['Only linear-order finite-r window','Not exact finite-dimensional entropy/purity extrema',
  'Not all-positive-order spectral rigidity','No unconditional phase selection when the gap vanishes with dimension']}
dump(folder/'REVIEW_SCOPE.json',scope)

ledger={
 'created_utc':now.isoformat(),'coverage':'This phase-4 author investigation, not rewriting prior stages',
 'actual_mathematical_control_failures_in_this_phase':[],
 'failure_statement':'No phase-4 mathematical control returned FAIL in the retained runs. Do not turn this into an independent PASS; preserve any later actual finding.',
 'entries':[
 {'kind':'SCOPE_GUARD','item':'Do not claim fixed-width H monotonicity outside v=w(Kx)-g(K)>0',
  'evidence':'At x->0 with fixed K, unconstrained H has behavior that does not yield an admissible interior h; root independently warned of this restriction',
  'resolution':'NO_ISLANDS explicitly proves only the admissible initial interval and uses that condition at the normalized increment inequality'},
 {'kind':'DISCOVERY_ONLY','item':'90-digit W=Wk candidate root',
  'files':['CRITICAL_EQUATION_DISCOVERY.json','explore_critical_equations.py'],
  'resolution':'Not an exhaustive root count or proof. Replaced as evidence by full exact intervals; original historical JSON retained'},
 {'kind':'DISCOVERY_ONLY','item':'Finite sufficient-bound and stationary-curve probes',
  'files':['MONOTONIC_SUFFICIENT_BOUNDS_DISCOVERY.json','STATIONARY_CURVE_DISCOVERY.json'],
  'resolution':'Never used as whole-domain sign proofs; analytic NO_ISLANDS and exact GLOBAL certificate provide those proofs'},
 {'kind':'AUTHOR_CONTROL_SUCCESS_NOT_REVIEW','item':'No-islands algebra and 92 admissible floating falsification points',
  'file':'NO_ISLANDS_AUTHOR_CONTROL.json','resolution':'Auxiliary only, does not approve the analytic theorem'},
 {'kind':'PREFREEZE_STRENGTHENING','item':'Critical interval producer added exact endpoint adjacency before freezing',
  'resolution':'No failed bound was discarded. Accepted final source/certificate and all exact mathematical leaves are bound; current replayer also validates every leaf'},
 {'kind':'AUTHOR_CONTROL_SUCCESS_NOT_REVIEW','item':'Critical 73-leaf full exact replay',
  'file':'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json','resolution':'All source/paper/certificate bytes bound; independent mathematical read still required'},
 {'kind':'AUTHOR_CONTROL_SUCCESS_NOT_REVIEW','item':'Global five scaling/derivative identities and 74-leaf exact partition replay',
  'files':['GLOBAL_TURN_ALGEBRA_CONTROL.json','GLOBAL_MIXED_AUTHOR_REPLAY.json'],
  'resolution':'Includes K=0 charts and seven explicit above-cap leaves; these are not omitted failures'},
 {'kind':'UPSTREAM_FINDING_REPORTED_BY_PARENT','item':'Root T-v1 omitted finite alpha>1 domain',
  'upstream_v1_sha256':'b270516f97cf719b2e64d4738d328d09d84ac133d8c44cc1620fd1126733e263',
  'upstream_v2_sha256':'83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79',
  'resolution':'Parent preserved v1 and corrected v2. Neither draft is a dependency here; all present max-moment/min-entropy statements explicitly retain alpha>1'},
 {'kind':'FROZEN_HISTORY','item':'Inherited README/TARGET and early discovery say full geometry open',
  'resolution':'Those are exact historical records, not silently rewritten. REVIEW_README and this new metadata describe author completion and pending independent status'},
 {'kind':'NEXT_UNFROZEN_RESEARCH','item':'Monotone coexistence derivative observation',
  'formulas':['M_c/M=4T x^2/[3(1-x)^2]>0','M_c/(2M)<g_prime(k)<g_prime(K)',
              'r_P_prime=M_c/(1-P)>0','r_B_prime=(2b_prime(K)-M_c)/P>0'],
  'resolution':'Author working observation only, not added to four frozen theorem scopes or claimed reviewed; preserve before the next research step'}
 ]}
dump(folder/'AUTHOR_ATTEMPT_LEDGER.json',ledger)
for name in ['REVIEW_README.md','THEOREM_MAP.md','REPRODUCE.md','build_review_metadata.py']:
    shutil.copyfile(aux/name,folder/name)
metadata_names=['REVIEW_README.md','THEOREM_MAP.md','REPRODUCE.md','SOURCE_INPUTS.json',
                'REVIEW_SCOPE.json','AUTHOR_ATTEMPT_LEDGER.json','build_review_metadata.py']
binding={'created_utc':now.isoformat(),'status':'Metadata ready for separate final ordinary binding, not yet approved',
 'frozen_proof_owner_commit':head,'frozen_input_count':len(frozen),
 'frozen_proof_input_bytes_unchanged':True,
 'metadata':[{'path':str(folder/name),'sha256':sha(folder/name),'bytes':(folder/name).stat().st_size} for name in metadata_names]}
dump(folder/'METADATA_BOUND_INPUTS.json',binding)
for entry in frozen:
    assert sha(repo/entry['path'])==entry['sha256'],entry['path']
archive=aux/f'four-scope-metadata-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert set(staged)=={prefix+'/'+name for name in metadata_names+['METADATA_BOUND_INPUTS.json']},staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: bind four-scope APPT phase review metadata and reproduction'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':newhead,'status':status,
 'metadata_bound_inputs_sha256':sha(folder/'METADATA_BOUND_INPUTS.json'),
 'source_inputs_sha256':sha(folder/'SOURCE_INPUTS.json'),'binding':binding,
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'four-scope-metadata-checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
