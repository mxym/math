from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess

repo=Path('/home/mxym/math-breadth-tcs-20261015')
root=Path('/home/mxym/math-appt-multiscale-20261013')
folder=repo/'research/breadth-tcs-20261015/phase-9-diverging-physical-reduction'
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-9-diverging-physical-reduction')
folder.mkdir(parents=True,exist_ok=True)
head='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
now=dt.datetime.now(dt.timezone.utc)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
names=[('research/appt-growing-renyi/PAPER.md','CORE: actual physical inequalities, exact kernel, pure spike and G1; complete prior read and relevant full sections reread'),
 ('research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md','CORE: V1,V17,V18 and exact calibrated benchmark; complete prior read, entire source reread14:07 including recovered finalsection6'),
 ('research/appt-ultralinear-spectrum-20261014/FAST_ORDER_SPECTRA.md','CORE exact body chord identity; separately RANGE fast-only classification; entire source reread14:02'),
 ('research/appt-ultralinear-spectrum-20261014/FAST_ORDER_VALUE.md','RANGE: exact fastbases and alln/alpha domain; first complete actual read14:02, not claimed read earlier'),
 ('research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md','ILLUSTRATION: mature actual value at lowercoexistence; complete prior source read retained'),
 ('research/appt-linear-critical-rigidity-20261015/PAPER.md','RANGE: actual finite(c,r) lossquantifiers, full source previously read and statements reread'),
 ('research/appt-growing-renyi/SPECTRAL_PROFILE.md','RANGE: complete finitegamma positive-order criteria; complete reread13:36'),
 ('research/appt-growing-renyi/UNIFORM_PROFILE.md','RANGE: credited earlier value coverage, not geometric classification; complete source previously read'),
 ('research/appt-growing-renyi/SMALL_ORDER_BOUNDARY.md','RANGE: finite tau,c Z2 boundary, full earlier read retained plus statements/section6 reread'),
 ('research/appt-multilevel-counterexample/PHASE_RIGIDITY.md','RANGE: finitegamma escaping secondmass andW1notW2; complete prior read retained')]
rows=[]
for name,scope in names:
    data=subprocess.check_output(['git','-C',str(root),'show',head+':'+name])
    dest=folder/'credited-inputs'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(data);dest.chmod(0o444)
    rows.append({'path':name,'sha256':sha(dest),'bytes':len(data),'commit':head,'actual_read_scope_and_role':scope})
global_source=repo/'research/breadth-tcs-20261015/phase-4-depth-appt/GLOBAL_MIXED_PHASE.md'
assert sha(global_source)=='5712392f1e74b9c1d1999bacb42cf21f0d0fac3c3cd963954774972dd487c4cb'
dest=folder/'credited-inputs'/'phase4'/'GLOBAL_MIXED_PHASE.md';dest.parent.mkdir(parents=True,exist_ok=True)
shutil.copyfile(global_source,dest);dest.chmod(0o444)
rows.append({'path':str(global_source),'sha256':sha(dest),'bytes':dest.stat().st_size,
 'actual_read_scope_and_role':'ILLUSTRATION only: complete author source, rootreported separate internal independent mathPASS; movingtie counterexample, not core reduction dependency'})
for name in ['PAPER.md','COVERAGE_AND_LIMITS.md','README.md','THEOREM_MAP.md','author_reduction_controls.py','AUTHOR_EXACT_CONTROLS.json','initialize_reduction_scope.py']:
    shutil.copyfile(aux/name,folder/name)
dump(folder/'SOURCE_INPUTS.json',{'created_utc':now.isoformat(),'root_capture_commit':head,'inputs':rows,
 'core_mathematical_dependencies':['G7-G18 physical/kernel/pole inputs andG1value','V1/V17/V18 calibrated value and excess','Exact FAST body chord identity, reproved in the new paper'],
 'illustration_dependencies':['MatureGLOBAL and L for the actual movingtie counterexample'],
 'not_dependencies':['S5 spectral criterion','PendingS6/S7/S8','Root developing zero-orderpath/value profiles','Restricted candidate spectrum model','Any new or expanded Lean audit'],
 'status':'New ordinary author physical reduction pending its independent full read; no complete geometric positive-axis assembly'})
dump(folder/'TARGET.json',{'created_utc':now.isoformat(),
 'domain':'Every original complex PSDtraceone density APPT under EVERY globalunitary,integers2<=m<=n,m->infinity,realalpha->infinity,unrestrictedalpha/m,alpha/D,n and arbitraryoscillation',
 'claims':['Nonleading exceptional centered powers uniformly negligible at momentEXCESS scale','All-state polynomial actualpeak domination and three-regime uniform entropylog reduction','Explicit creditedV* relativeEXCESS benchmark validallalpha∞','Necessaryandsufficient actualspectralfunctional tests with actualmean,width,fraction andexact chordloss'],
 'actual_functional':'Z=[Halpha(y1)+N{[mu/(1+kappatheta)]^alpha[1+theta Zk(1-Lambda)]-1-alpha(mu-1)}]/D>=0,C=1+Z>=1',
 'must_keep':['Exactu_D','ActualLambda','Actualmean before exponentiation and linearcentering','TinyM*-1 lowerbound','Positivekernel ratio monotone onlyeventuallyalpha>=2','Three exhaustivechi regimes','RelativeEXCESS notraw accuracy','Noinstantaneousexactargmaxdistance substitution'],
 'status':'Complete authorproof, independentreviewpending; not geometric fullpositiveaxis ornewmajor'})
dump(folder/'PRIMARY_SCREEN.json',{'recorded_utc':now.isoformat(),
 'discovery_history':'New physical reduction arose during compatibility reading after14:02 and before14:08:29, prior to the additional exact-term query; earlier broad APPT spectral/entropy primary-domain screens had returned no matching results',
 'additional_actual_search_time_window_utc':['2026-10-15T14:14:24.5584625Z','2026-10-15T14:15:41Z'],
 'queries':['"absolutely PPT" "spectral" "reduction" entropy','"absolute PPT" "all orders" spectral','"APPT" "centered" "entropy"'],
 'domains':['arxiv.org'],'result':'No results returned for those bounded exact official-primary-domain queries',
 'limit':'Not exhaustive literature, historicalpriority, external fullpaperread or a claim that no related reduction exists; mature local kernel/chord/value inputs explicitly credited'})
dump(folder/'ATTEMPT_LEDGER.json',{'created_utc':now.isoformat(),'scope':'S9 universal diverging-order physical reduction',
 'actual_math_or_tool_failures_this_scope':[],
 'unfrozen_author_clarification':'Initial draft reused rho for the state and the15/16rate; changed rate torho0 before freezing or controls; no failed mathematical control was removed',
 'retained_excluded_inferences':['Logging a coarse optimum-relative additiveerror does not prove entropyerror','Dropping actualmean whenalpha≫D','Dropping a smallchordloss at firstnonzero scale','UsingrawVaccuracy to inferexcessaccuracy nearone','Replacing valuecriterion byinstantaneousexactargmaxdistance','Inferring allpositivegeometricclassification or pendingcomponentPASS'],
 'author_controls':'47 exact actual spectra includingalpha>D,singular,constantbody,nonzerochordloss andactualmean; all requested Fraction assertions passed, no finiteM* computed',
 'scope_status':'Only this direct newproof; mature inputs credited, componentstatus preserved; no root/Lean/index/publication action'})
print(json.dumps({'utc':now.isoformat(),'folder':str(folder),'paper_sha256':sha(folder/'PAPER.md'),
 'paper_bytes':(folder/'PAPER.md').stat().st_size,'source_inputs_sha256':sha(folder/'SOURCE_INPUTS.json'),
 'inputs':len(rows)},indent=2))
