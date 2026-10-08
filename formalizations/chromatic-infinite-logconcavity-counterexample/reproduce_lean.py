#!/usr/bin/env python3
"""Prepare a new external replay workspace using existing pinned Lean assets.
No installation or download. --run starts fresh compilation and kernel replay.
"""
from pathlib import Path
if not __debug__:
    raise SystemExit('Run without Python -O or PYTHONOPTIMIZE: assertions are required.')
import argparse,json,shutil,subprocess,sys
B=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--toolchain',type=Path,required=True,help='Existing Lean 4.34.1 toolchain root')
ap.add_argument('--packages-root',type=Path,required=True,help='Existing pinned git checkouts and compiled dependency libraries, one directory per package name')
ap.add_argument('--workdir',type=Path,required=True,help='New, nonexistent writable directory outside this public snapshot')
ap.add_argument('--cache-root',type=Path,help='Optional recorded cache location (verification does not download)')
ap.add_argument('--run',action='store_true',help='Actually run doctor and fresh verification; otherwise prepare only')
a=ap.parse_args()
W=a.workdir.resolve()
if W.exists():ap.error('--workdir must not already exist')
if W==B or B in W.parents:ap.error('--workdir must be outside the public evidence snapshot')
if a.run and not (a.toolchain/'bin/lean').is_file():ap.error('Lean executable missing')
for p in [a.toolchain/'bin/lean',a.packages_root]:
    if not p.exists():ap.error('Required existing asset missing: '+str(p))
subprocess.run([sys.executable,str(B/'check_public.py')],check=True)
W.mkdir(parents=True)
for sub in ['bin','checks']:shutil.copytree(B/'evidence/verifier'/sub,W/sub)
for sub in ['config','locks','tasks']:(W/sub).mkdir()
cfg=json.loads((B/'evidence/verifier/config/environment.json').read_text())
cfg['toolchain_path']=str(a.toolchain.resolve())
cfg['packages_root']=str(a.packages_root.resolve())
cfg['cache_root']=str(a.cache_root.resolve()) if a.cache_root else str(W/'cache')
(W/'cache').mkdir()
(W/'config/environment.json').write_text(json.dumps(cfg,indent=2)+'\n')
case=json.loads((B/'evidence/formalization/verify.json').read_text())
case['source_dir']=str((B/'evidence/formalization/sources').resolve())
(W/'config/chromatic-c17.json').write_text(json.dumps(case,indent=2)+'\n')
cmd=[sys.executable,str(W/'bin/leanctl.py')]
print('Prepared '+str(W),flush=True)
print('Run: '+' '.join(cmd+['doctor']),flush=True)
print('Run: '+' '.join(cmd+['verify',str(W/'config/chromatic-c17.json')]),flush=True)
if a.run:
    subprocess.run(cmd+['doctor'],check=True)
    subprocess.run(cmd+['verify',str(W/'config/chromatic-c17.json')],check=True)
