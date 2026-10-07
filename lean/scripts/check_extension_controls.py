#!/usr/bin/env python3
"""Extra fail-closed and geometric-meaning controls for the additive 33 exports."""
from pathlib import Path
import json,os,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parent.parent
LOGS=ROOT/'logs';ROWS=[]
MODE='optimized' if os.environ.get('PYTHONOPTIMIZE') else 'normal'
DEST=LOGS/('extension-controls-'+MODE);DEST.mkdir(exist_ok=True)
def run(label,args,cwd,diagnostic=None):
 p=subprocess.run(args,cwd=cwd,capture_output=True,text=True)
 output=(p.stdout+p.stderr).replace(str(ROOT),'<project>')
 (DEST/(label+'.log')).write_text(output)
 passed=(p.returncode==0) if diagnostic is None else (p.returncode!=0 and diagnostic in output)
 ROWS.append(dict(name=label,command=[a.replace(str(ROOT),'<project>') for a in args],actual_exit=p.returncode,negative=diagnostic is not None,passed=passed,expected_diagnostic=diagnostic))
 if not passed:raise RuntimeError('Control failed '+label+': '+output)
 return output
with tempfile.TemporaryDirectory(prefix='extension-controls-',dir=ROOT/'.lake') as tmp:
 TEMP=Path(tmp)
 def report_copy(label):
  p=TEMP/label;(p/'scripts').mkdir(parents=True);(p/'logs').mkdir()
  shutil.copyfile(ROOT/'scripts/check_axioms.py',p/'scripts/check_axioms.py')
  shutil.copyfile(ROOT/'exported-theorems.json',p/'exported-theorems.json')
  return p
 original=(ROOT/'logs/axioms.log').read_text()
 new=[e for e in json.loads((ROOT/'exported-theorems.json').read_text()) if e['name'].startswith(('Entry005.','Mxym.StochasticRigidity.'))]
 if len(new)!=33:raise RuntimeError('Expected exactly 33 additive exports')
 for i,e in enumerate(new):
  p=report_copy('missing-'+str(i));line=next(s for s in original.splitlines(keepends=True) if s.startswith("'"+e['name']+"'"))
  (p/'logs/axioms.log').write_text(original.replace(line,''))
  run('missing-'+e['name'],['python3','scripts/check_axioms.py'],p,'Missing or unexpected #print axioms result')
 for label,tail in [('extraneous','error: simulated Lean failure\n'),('trailing-garbage','arbitrary text\n')]:
  p=report_copy(label);(p/'logs/axioms.log').write_text(original+tail)
  run(label,['python3','scripts/check_axioms.py'],p,'Malformed or extraneous axiom output')
 p=report_copy('duplicate-export');(p/'logs/axioms.log').write_text(original)
 data=json.loads((p/'exported-theorems.json').read_text());data[-1]=data[0]
 (p/'exported-theorems.json').write_text(json.dumps(data))
 run('duplicate-export',['python3','scripts/check_axioms.py'],p,'Expected 101 distinct audited exports')
 def project_copy(label):
  p=TEMP/label
  shutil.copytree(ROOT,p,ignore=shutil.ignore_patterns('.lake','logs','__pycache__'))
  shutil.copytree(ROOT/'logs',p/'logs',ignore=shutil.ignore_patterns('extension-controls-*','verification-*','control-*','controls-summary*'))
  (p/'.lake').symlink_to(ROOT/'.lake',target_is_directory=True)
  return p
 for label,fixture,diag in [('skip-kernel','set_option debug.skipKernelTC true','Forbidden kernel-check option'),('opaque','opaque fakeVolume : Nat := 0','Forbidden proof escape'),('extern','@[extern "fake"] def fakeExternal : Nat := 0','Forbidden proof escape')]:
  p=project_copy(label);f=p/'Entry005/ProjectionCap.lean';f.write_text(f.read_text()+'\n'+fixture+'\n')
  run(label,['python3','scripts/generate_audit.py'],p,diag)
 p=project_copy('baseline-proof');f=p/'Mxym/NormedBalance.lean';f.write_text(f.read_text()+'\n-- altered frozen proof bytes\n')
 run('baseline-proof',['python3','scripts/check_baseline.py'],p,'Protected baseline bytes changed')
 p=project_copy('coverage-inventory');data=json.loads((p/'axiom-report.json').read_text());data[-1]['name']='Control.unexpected'
 (p/'axiom-report.json').write_text(json.dumps(data))
 run('coverage-inventory',['python3','scripts/generate_coverage.py'],p,'Stored coverage axiom inventory differs from fresh audited output')
 # Regressions for independently identified standalone reporting holes.
 p=project_copy('extra-dependency');manifest=json.loads((p/'lake-manifest.json').read_text())
 manifest['packages'].append(dict(manifest['packages'][0],name='unreviewedDependency'))
 (p/'lake-manifest.json').write_text(json.dumps(manifest))
 run('extra-dependency',['python3','scripts/check_pins.py'],p,'Missing, duplicated or unexpected locked package')
 for label,mutate,diagnostic in [
   ('checkout-origin','origin','plausible: checkout origin differs'),
   ('untracked-source','untracked','plausible: source checkout is modified')]:
  p=TEMP/label;(p/'scripts').mkdir(parents=True);(p/'.lake/packages').mkdir(parents=True)
  shutil.copyfile(ROOT/'scripts/check_pins.py',p/'scripts/check_pins.py')
  for file in ['lean-toolchain','lakefile.toml','lake-manifest.json']:shutil.copyfile(ROOT/file,p/file)
  for package in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
   name=package['name']
   if name!='plausible':(p/'.lake/packages'/name).symlink_to(ROOT/'.lake/packages'/name,target_is_directory=True)
  clone=p/'.lake/packages/plausible'
  subprocess.run(['git','clone','--quiet','--shared',str(ROOT/'.lake/packages/plausible'),str(clone)],check=True)
  subprocess.run(['git','remote','set-url','origin','https://github.com/leanprover-community/plausible'],cwd=clone,check=True)
  if mutate=='origin':subprocess.run(['git','remote','set-url','origin','https://example.invalid/unreviewed.git'],cwd=clone,check=True)
  else:(clone/'UntrackedSource.lean').write_text('def untrackedFixture : Nat := 0\n')
  run(label,['python3','scripts/check_pins.py'],p,diagnostic)
 # Recheck four geometrically wrong variants directly in the genuine original project environment.
 original=(ROOT/'Entry005/ProjectionCap.lean').read_text()
 mutations={
  'missing-deficit':original.replace('    (hdef : ∀ u : E, ‖u‖ = 1 →\n      (projectedVolume (ℝ ∙ u)ᗮ P).toReal -\n        (projectedVolume (ℝ ∙ u)ᗮ K).toReal ≤ η) :','    :'),
  'strict-zero-endpoint':original.replace('Metric.hausdorffDist (K : Set E) (P : Set E) ≤','Metric.hausdorffDist (K : Set E) (P : Set E) <'),
  'fake-ambient-volume':original.replace('volume (projectBody U K : Set U)',"volume ((fun x : U => (x : E)) '' (projectBody U K : Set U))"),
  'wrong-dimension':original.replace('  let m := Module.finrank ℝ E - 1','  let m := Module.finrank ℝ E')}
 for label,text in mutations.items():
  if text==original:raise RuntimeError('Mutation made no change: '+label)
  p=TEMP/label;(p/'Entry005').mkdir(parents=True);f=p/'Entry005/ProjectionCap.lean';f.write_text(text)
  out=run(label,['lake','env','lean','--root='+str(p),str(f)],ROOT,'error')
  if 'input file must be contained' in out:raise RuntimeError('Bad control compilation root')
negative=sum(row['negative'] for row in ROWS)
report=dict(mode=MODE,negative_checks=negative,negative_passed=sum(row['negative'] and row['passed'] for row in ROWS),controls=ROWS)
(DEST/'summary.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print('PASS: '+str(negative)+' additive-module negative controls in '+MODE+' Python.')
