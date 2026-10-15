from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-9-diverging-physical-reduction'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-9-diverging-physical-reduction')
now=dt.datetime.now(dt.timezone.utc);tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert head=='d7e77657df525e0e1ac49aaffeb97bcfbd810a09'
shutil.copyfile(aux/'freeze_reduction_scope.py',folder/'freeze_reduction_scope.py')
controls=json.loads((folder/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert controls['all_requested_assertions_passed'] and controls['finite_cases']==47
assert controls['paper_sha256']==sha(folder/'PAPER.md')
assert controls['source_sha256']==sha(folder/'author_reduction_controls.py')
assert sha(folder/'PAPER.md')=='812ba384981a4ed6ae1ae62d93723fc0505609b7ecf7997c452331947ffcb078'
before=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1','-uall']).decode()
for line in before.splitlines():assert line[3:].startswith(prefix+'/'),line
manifest={'frozen_utc':now.isoformat(),'status':'Complete new ordinary author scope, distinct independent full review pending',
 'owner':'/root/breadth_tcs_resume_20261015 APPT depth role',
 'source_root_commit':'1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f',
 'domain':'Every original complex PSDtraceone APPT density underEVERY globalunitary,2<=m<=n,m->infinity,realalpha->infinity,alln and unrestrictedalpha/m,alpha/D witharbitraryoscillation',
 'core_claims':['Uniform exponential optimalmomentEXCESS reduction of nonleading exceptional kernels','All-state polynomial actualpeakcomparison','Three-regime uniform relativeentropylog reduction includingtinyM*-1','Exact finite actualmean/width/fraction/chordloss expression','MatureV* relativeEXCESS corollary acrossallalpha∞','Necessaryandsufficient explicitbenchmark actualspectralfunctional tests'],
 'illustration_claims':['Actual integer-rank movingcoexistence counterexample toinstantaneousexactargmaxdistance, explicitly creditsmatureGLOBAL/L'],
 'read_scope_required':['Entire PAPER','Exact actualbodyloss/mean and kernelpositivity','Actualpurepole lowerbound at tinyexcess','Positivekernel/x^2 monotonic onlyalpha>=2','Polynomialcomparison for bothactualpeakcases','Everychi regime anduniformdivision','G1/V18/V1/V17 excessbenchmarkbridge','Alln/orderoscillation withoutalpha/m restriction','Movingtie counterexample andcoverage/status exclusions'],
 'not_dependencies':['S5 spectral criterion','PendingS6/S7/S8','Root developingzero-order orvalue profiles','Restrictedcandidate APPT model','NewLean orbroadenedoldaudit'],
 'not_claimed':['Geometricfullpositiveaxisclassification','Fixedm orboundedalpha oralpha0 theorem','Finiteexactoptimum','Historicalfirst or externalhumanreview','Newmajorcount'],
 'reproduction':'Copy PAPER.md andauthor_reduction_controls.py to a freshprivatescratch and runpython3; compare exactmathematicalrows/source/paperhashes, allownewUTC; do not overwrite frozenproducer outputs',
 'files':[{'path':p.relative_to(folder).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
          for p in sorted(folder.rglob('*')) if p.is_file()],
 'publication':'No rootedit,push,index,Release,DOI,preprint,externalmessage orLean action; author-only'}
dump(folder/'AUTHOR_V1_MANIFEST.json',manifest)
for p in folder.rglob('*'):
    if p.is_file():p.chmod(0o444)
archive=aux/f'diverging-reduction-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert all(p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: author all-diverging-order APPT physical kernel reduction'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'parent_head':head,'head':newhead,'status':status,
 'paper':{'path':str(folder/'PAPER.md'),'sha256':sha(folder/'PAPER.md'),'bytes':(folder/'PAPER.md').stat().st_size},
 'manifest_sha256':sha(folder/'AUTHOR_V1_MANIFEST.json'),
 'controls_sha256':sha(folder/'AUTHOR_EXACT_CONTROLS.json'),
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
