#!/usr/bin/env python3
"""Interactive development diagnostics, NOT a proof verification certificate.

Only validated Lean source paths and module names are accepted. Every request
gets a fresh owned-object directory. The independent source-bound proof CI is
separate and must succeed before a formalization checkpoint is certified.
"""
from pathlib import Path
import base64, hashlib, json, os, re, shutil, subprocess, time, urllib.request, urllib.error

REPO='mxym/math'
INPUT_REF='formal/hydrology-tree-compiler-input-20261011'
OUTPUT_REF='formal/hydrology-tree-compiler-results-20261011'
BASE=Path(os.environ['GITHUB_WORKSPACE'])/'formalizations/hydrology-tree-core'
OUT=Path(os.environ['RUNNER_TEMP'])/'tree-compiler-session'
OUT.mkdir(parents=True,exist_ok=True)
TOKEN=os.environ['GH_TOKEN']
START=time.monotonic()

def api(method,path,data=None):
 request=urllib.request.Request('https://api.github.com/repos/'+REPO+'/'+path,
     data=None if data is None else json.dumps(data).encode(),method=method,
     headers={'Authorization':'Bearer '+TOKEN,'Accept':'application/vnd.github+json',
              'X-GitHub-Api-Version':'2022-11-28','User-Agent':'math-lean-development-compiler'})
 for retry in range(4):
  try:
   with urllib.request.urlopen(request,timeout=30) as f:
    raw=f.read();return json.loads(raw) if raw else None
  except urllib.error.HTTPError as e:
   if e.code==404:return None
   if e.code in (429,500,502,503,504) and retry<3:time.sleep(2**retry);continue
   raise
  except (TimeoutError,urllib.error.URLError):
   if retry==3:raise
   time.sleep(2**retry)

def ensure_branch(ref):
 if api('GET','git/ref/heads/'+ref) is None:
  api('POST','git/refs',{'ref':'refs/heads/'+ref,'sha':os.environ['GITHUB_SHA']})

def put(path,content,message):
 old=api('GET','contents/'+path+'?ref='+OUTPUT_REF)
 data={'branch':OUTPUT_REF,'message':message,'content':base64.b64encode(content).decode()}
 if old:data['sha']=old['sha']
 api('PUT','contents/'+path,data)

def publish(report,log=''):
 report['scope']='DEVELOPMENT_DIAGNOSTICS_ONLY; not empty-kernel or full-theorem certification'
 report['run_id']=os.environ['GITHUB_RUN_ID']
 put('compiler/latest.json',(json.dumps(report,indent=2)+'\n').encode(),
     'Lean development compiler receipt '+str(report.get('serial',report['status'])))
 if log:put('compiler/diagnostics.log',log.encode(),'Preserve literal development diagnostics')
 print(json.dumps({k:v for k,v in report.items() if k not in ('diagnostics','source_sha256')}),flush=True)

for ref in (INPUT_REF,OUTPUT_REF):ensure_branch(ref)
lean=Path(shutil.which('lean')).resolve()
packages=BASE/'.lake/packages'
paths=[str(p/'.lake/build/lib/lean') for p in packages.iterdir() if p.is_dir()]
publish({'status':'READY','base_commit':os.environ['GITHUB_SHA']})
last=None
while time.monotonic()-START<3300:
 raw=api('GET','contents/compiler/request.json?ref='+INPUT_REF)
 if raw is None or raw['sha']==last:time.sleep(5);continue
 last=raw['sha'];request=json.loads(base64.b64decode(raw['content']))
 serial=request.get('serial')
 if not isinstance(serial,int) or serial<0:raise ValueError('Nonnegative integer serial required')
 if request.get('stop'):
  publish({'serial':serial,'status':'STOPPED','request_blob':last});break
 files=request.get('files',{});modules=request.get('modules',[])
 if len(files)>150 or len(modules)>150:raise ValueError('Request too large')
 for name,text in files.items():
  if not re.fullmatch(r'(?:[A-Za-z_][A-Za-z_0-9]*/)*[A-Za-z_][A-Za-z_0-9]*\.lean',name):raise ValueError('Unsafe Lean path')
  if not isinstance(text,str) or len(text)>300000:raise ValueError('Source text too large')
 for module in modules:
  if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',module):raise ValueError('Invalid module name')
 work=OUT/('request-'+str(serial)+'-'+last[:8]);work.mkdir()
 for module in modules:
  name=module.replace('.','/')+'.lean'
  text=files.get(name)
  if text is None:text=(BASE/name).read_text()
  target=work/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
 imports=set()
 for source in work.rglob('*.lean'):
  for line in source.read_text().splitlines():
   if re.fullmatch(r'import Mathlib\.[A-Za-z_0-9.]+',line):imports.add(line.split()[1])
 env=os.environ.copy();env.pop('GH_TOKEN',None);env.pop('GITHUB_TOKEN',None)
 env['LEAN_PATH']=os.pathsep.join([str(work)]+paths);env.pop('LEAN_SRC_PATH',None)
 report={'serial':serial,'status':'COMPILING','request_blob':last,'modules':modules,
         'source_sha256':{str(p.relative_to(work)):hashlib.sha256(p.read_bytes()).hexdigest() for p in work.rglob('*.lean')},'commands':[]}
 publish(report)
 logs=[]
 if imports:
  cache_env=env.copy();cache_env.pop('LEAN_PATH',None)
  cache=subprocess.run([str(lean.parent/'lake'),'exe','cache','get',*sorted(imports)],
      cwd=BASE,env=cache_env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
  logs.append('CACHE\n'+cache.stdout)
  if cache.returncode:report['status']='CACHE_ERROR'
 if report['status']=='COMPILING':
  for module in modules:
   name=module.replace('.','/');start=time.monotonic()
   try:
    p=subprocess.run([str(lean),'-j2','-o',name+'.olean',name+'.lean'],cwd=work,env=env,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
    text=p.stdout;rc=p.returncode
   except subprocess.TimeoutExpired as e:
    rc=124;text='COMPILER TIMEOUT\n'+str(e.stdout or '')
   logs.append('MODULE '+module+'\n'+text)
   record={'module':module,'returncode':rc,'seconds':round(time.monotonic()-start,3)}
   report['commands'].append(record)
   if rc:
    report['status']='COMPILER_ERROR';report['diagnostics']=text[-40000:];break
  else:report['status']='COMPILED'
 log='\n'.join(logs);(work/'diagnostics.log').write_text(log)
 (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 publish(report,log)
else:
 publish({'status':'SESSION_EXPIRED','last_request_blob':last})
