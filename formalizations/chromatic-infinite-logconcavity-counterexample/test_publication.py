from pathlib import Path
if not __debug__:
    raise SystemExit('Run without Python -O or PYTHONOPTIMIZE: assertions are required.')
import tempfile, shutil, subprocess, sys, json, hashlib
SRC=Path(__file__).resolve().parent
checks=[]
def run(args,cwd,ok=True):
 r=subprocess.run([sys.executable,'-B']+args,cwd=cwd,text=True,capture_output=True)
 assert (r.returncode==0)==ok,(args,r.returncode,r.stdout,r.stderr)
 return r
with tempfile.TemporaryDirectory(prefix='chromatic-public-test-') as td:
 T=Path(td); B=T/'public snapshot';shutil.copytree(SRC,B)
 initial={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for p in B.rglob('*') if p.is_file()}
 run(['check_public.py'],B);checks.append('Full inventory, complete historical projection, graph, declarations, axioms, source bindings, recorded commands, and all exact C17 arithmetic pass')
 for script in ['check_public.py','audit/audit_record.py','reproduce_lean.py','test_publication.py']:
  r=subprocess.run([sys.executable,'-O','-B',script],cwd=B,text=True,capture_output=True)
  assert r.returncode!=0 and 'assertions are required' in r.stderr+r.stdout
 checks.append('All four assertion-based public entry points fail closed under Python -O')
 p=B/'evidence/formalization/sources/CycleColoring.lean';old=p.read_bytes();p.write_bytes(old+b'\n')
 run(['check_public.py'],B,False);p.write_bytes(old);checks.append('Changed Lean source rejected')
 p=B/'unexpected.txt';p.write_text('not manifested');run(['check_public.py'],B,False);p.unlink();checks.append('Unexpected unmanifested file rejected')
 p=B/'CURRENT_PUBLIC_MANIFEST.json';old=p.read_bytes();m=json.loads(old);m['files'].append(m['files'][0]);p.write_text(json.dumps(m));run(['check_public.py'],B,False);p.write_bytes(old);checks.append('Duplicate public manifest entry rejected')
 p=B/'evidence/fresh-verification/manifest/all-owned-closure.json';old=p.read_bytes();p.write_bytes(old[:-10]);run(['check_public.py'],B,False);p.write_bytes(old);checks.append('Truncated closure evidence rejected')
 assets=T/'synthetic path with spaces';(assets/'toolchain/bin').mkdir(parents=True);(assets/'packages').mkdir()
 marker=assets/'MUST_NOT_RUN';fake=assets/'toolchain/bin/lean';fake.write_text('#!/bin/sh\ntouch "'+str(marker)+'"\nexit 91\n');fake.chmod(0o755)
 common=['reproduce_lean.py','--toolchain',str(assets/'toolchain'),'--packages-root',str(assets/'packages')]
 W=T/'prepared external replay';run(common+['--workdir',str(W)],B)
 assert not marker.exists();cfg=json.loads((W/'config/environment.json').read_text());orig=json.loads((B/'evidence/verifier/config/environment.json').read_text())
 assert {k:v for k,v in cfg.items() if k not in ['toolchain_path','packages_root','cache_root']}=={k:v for k,v in orig.items() if k not in ['toolchain_path','packages_root','cache_root']}
 assert (W/'bin/leanctl.py').read_bytes()==(B/'evidence/verifier/bin/leanctl.py').read_bytes()
 case=json.loads((W/'config/chromatic-c17.json').read_text());origcase=json.loads((B/'evidence/formalization/verify.json').read_text())
 assert {k:v for k,v in case.items() if k!='source_dir'}=={k:v for k,v in origcase.items() if k!='source_dir'}
 assert case['source_dir']==str((B/'evidence/formalization/sources').resolve())
 assert not list(W.rglob('*.olean')) and not list(W.rglob('*.ilean'))
 checks.append('Prepare-only supports spaces, preserves all pins/scope/roots/source hashes, copies exact verifier/checks, imports no owned binaries, and never invokes synthetic Lean')
 run(common+['--workdir',str(W)],B,False);checks.append('Existing output directory rejected')
 run(common+['--workdir',str(B/'forbidden')],B,False);checks.append('Output inside public snapshot rejected')
 run(['reproduce_lean.py','--toolchain',str(T/'missing'),'--packages-root',str(assets/'packages'),'--workdir',str(T/'missing-output')],B,False);checks.append('Missing toolchain asset rejected')
 run(['audit/audit_record.py','--output',str(B/'bad-output.json')],B,False);checks.append('Portable audit refuses output inside public snapshot')
 after={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for p in B.rglob('*') if p.is_file()}
 assert initial==after;checks.append('All original public snapshot files unchanged after positive and negative tests')
print(json.dumps({'status':'PASS','scope':'Python static/publication and prepare-only controls; no Lean compiler or kernel invoked','checks':checks},indent=2))
