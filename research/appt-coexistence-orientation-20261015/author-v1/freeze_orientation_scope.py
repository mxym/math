from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
root=Path('/home/mxym/math-appt-multiscale-20261013')
prefix='research/breadth-tcs-20261015/phase-8-coexistence-orientation'
folder=repo/prefix
old=repo/'research/breadth-tcs-20261015/phase-4-depth-appt'
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-8-coexistence-orientation')
folder.mkdir(parents=True,exist_ok=True)
now=dt.datetime.now(dt.timezone.utc);tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert head=='fe140c31f698b4c9ac8cc18ba5661695755b0099'
frozen={
 'GLOBAL_MIXED_PHASE.md':'5712392f1e74b9c1d1999bacb42cf21f0d0fac3c3cd963954774972dd487c4cb',
 'CRITICAL_UNIQUENESS_CERTIFICATE.md':'be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e',
 'NO_ISLANDS.md':'f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16',
 'LAST_MIXED_BOUNDARY.md':'6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0'}
rows=[]
for name,expected in frozen.items():
    source=old/name
    assert sha(source)==expected,name
    dest=folder/'credited-inputs'/'phase4'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,dest);dest.chmod(0o444)
    rows.append({'path':str(source),'sha256':sha(dest),'bytes':dest.stat().st_size,
     'actual_read_scope':'Complete author source and complete derivative/coexistence/triple statements retained in this role; root reports separate independent full mathematical PASS',
     'role':'Credited complete geometry ordinary input; original exact certificate/review scopes unchanged'})
roothead='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
for name in ['research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md',
 'research/appt-linear-critical-rigidity-20261015/PAPER.md']:
    data=subprocess.check_output(['git','-C',str(root),'show',roothead+':'+name])
    dest=folder/'credited-inputs'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data);dest.chmod(0o444)
    rows.append({'path':name,'sha256':sha(dest),'bytes':len(data),'commit':roothead,
     'actual_read_scope':'Complete prior L/S read retained; S definitions/full iff/allquantum transfer statements reread before this note',
     'role':'Credited original complex all-global-unitary APPT value/actual-nearoptimizer transfer'})
for name in ['PAPER.md','README.md','THEOREM_MAP.md','freeze_orientation_scope.py']:
    shutil.copyfile(aux/name,folder/name)
dump(folder/'SOURCE_INPUTS.json',{'created_utc':now.isoformat(),'inputs':rows,
 'new_result':'Global orientation and every fixed-r slice of the fully classified scalar phase diagram, with exact fixed-parameter derivative conventions and actual finite(c,r) S transfer',
 'not_dependencies':['Pending S5/S6/S7','Root developing fullzero-order or all-dimension value syntheses'],
 'review_status':'This note pending its own independent full ordinary read; earlier inputs internal mathematical PASS reported byroot, final metadata binding separate',
 'no_new_certificate':'Existing interval engines/certificates are theorem dependencies in their frozen original scopes; no producer/replay or old audit enlarged'})
dump(folder/'TARGET.json',{'created_utc':now.isoformat(),
 'scalar_domain':'Every realc>0,r>=0,full compact(L,h) scalar optimization; complete ordinary geometry input',
 'quantum_domain':'Every original complex all-global-unitary APPT density sequence,m->infinity,n>=m,realalpha>1,alpha/m->finitepositivec,3^alpha/(mn)->finiter',
 'claims':['Both coexistence derivatives strictly positive globally andat triple','Endpoints0/r_star and inverse analyticity','Every fixed-r c slice with allties and no repeatedmixed interval','Horizontal linear closing','Original S iff transfer retaining actual J and Pi'],
 'derivative_conventions':['M_c atfixedr alongstationarybranch','f_c atfixedk,r','separate f_c atfixedL,r with chain2x f_k','a_k atfixedc orK','Total d/dc alongr_B/P only after envelopepartials'],
 'not_claimed':['New interval certificate','Whole positive-axis quantum synthesis','Exact finite maximizers','Priority/externalhumanreview','New Lean or major count'],
 'status':'Complete new ordinary author scope pending its independent read'})
dump(folder/'ATTEMPT_LEDGER.json',{'created_utc':now.isoformat(),
 'origin':'Derivative observation first preserved unfrozen in phase4 author ledger; now fully checked and completed as a separate new scope',
 'local_collision_screen':'Native rg of current root linear-phase scientific sources did not find this global coexistence monotonicity/fixed-r theorem; absence is not historical priority',
 'actual_tool_or_math_failures_this_scope':[],
 'retained_parameter_errors_excluded':['Identifying fixedL andfixedk cpartials before stationarity','Treating M_c as totalderivative alongcoexistence','Replacing M_r by a normalizedweight differentfrom originalP','Inferring hprime>0 from genericstrictincrease','Extrapolating S outof finite(c,r) window'],
 'new_checks':'Pure analytic proof; no finite grid or testproducer mirrors the derivative formulas, no old certificate rewritten orrerun',
 'scope_status':'Author-only newnote; no root edits,push,Lean,index orsubmission'})
manifest={'frozen_utc':now.isoformat(),'owner':'/root/breadth_tcs_resume_20261015 APPT depth role',
 'status':'Complete new ordinary author argument, distinct independent review pending',
 'read_scope_required':['Entire PAPER','Exact derivative parameterholding andchainrule','Nondegeneratebranch envelope','Positivity andstrictbulk comparison','Smallc thresholduniformbound','Global inverses/endpoints/allties','Actual S full lossconditions andfinitewindowquantifiers'],
 'not_claimed':['New computerassisted certificate','Expanded old independent orLean audit','PendingS5/S6/S7 assembly','Newmajorcount orpriority'],
 'files':[{'path':p.relative_to(folder).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
          for p in sorted(folder.rglob('*')) if p.is_file()],
 'reproduction':'Read explicit analytic formulas/identities and credited frozen theorems; no new numerical or exact certificate producer is partof thisscope'}
dump(folder/'AUTHOR_V1_MANIFEST.json',manifest)
for p in folder.rglob('*'):
    if p.is_file():p.chmod(0o444)
archive=aux/f'orientation-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert all(p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: author APPT coexistence orientation and complete fixed-r slices'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'parent_head':head,'head':newhead,'status':status,
 'paper':{'path':str(folder/'PAPER.md'),'sha256':sha(folder/'PAPER.md'),'bytes':(folder/'PAPER.md').stat().st_size},
 'manifest_sha256':sha(folder/'AUTHOR_V1_MANIFEST.json'),
 'source_inputs_sha256':sha(folder/'SOURCE_INPUTS.json'),
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
