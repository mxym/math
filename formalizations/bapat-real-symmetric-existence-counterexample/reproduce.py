#!/usr/bin/env python3
"""Rebuild and replay this package with existing pinned official dependencies."""
import argparse,json,pathlib,shutil,subprocess,sys
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--toolchain',required=True,type=pathlib.Path)
ap.add_argument('--packages-root',required=True,type=pathlib.Path)
ap.add_argument('--output',required=True,type=pathlib.Path)
a=ap.parse_args(); bundle=pathlib.Path(__file__).resolve().parent
out=a.output.resolve(); out.mkdir(parents=True,exist_ok=False)
for folder in ['bin','checks','config','locks','tasks']:(out/folder).mkdir()
for name in ['bin/leanctl_signatures_v1.py','checks/OwnedAudit.standard-axioms-v1.template.lean','checks/RejectInvalidProof.lean']:
 shutil.copy2(bundle/'verifier'/name,out/name)
c=json.loads((bundle/'verifier/config/environment.json').read_text())
c['toolchain_path']=str(a.toolchain.resolve()); c['packages_root']=str(a.packages_root.resolve()); c['cache_root']=str(out/'unused-cache')
(out/'config/environment.json').write_text(json.dumps(c,indent=2)+'\n')
t=json.loads((bundle/'formalization/verify.json').read_text());t['source_dir']=str(bundle/'formalization/sources')
(out/'case.json').write_text(json.dumps(t,indent=2)+'\n')
raise SystemExit(subprocess.call([sys.executable,str(out/'bin/leanctl_signatures_v1.py'),'verify',str(out/'case.json')]))
