#!/usr/bin/env python3
"""Reproducible proof examples and negative reporting controls; no downloads or source edits."""
from pathlib import Path
import concurrent.futures
import json
import os
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent.parent
LOGS=ROOT/'logs'
LOGS.mkdir(exist_ok=True)
ENV=dict(os.environ)
if not ENV.get('ELAN_HOME') and (ROOT/'.elan/bin/elan').exists():
 ENV['ELAN_HOME']=str(ROOT/'.elan')
if ENV.get('ELAN_HOME'):
 ENV['PATH']=str(Path(ENV['ELAN_HOME'])/'bin')+':'+ENV['PATH']
ENV['ELAN_TOOLCHAIN']='leanprover/lean4:v4.34.1'
rows=[]

def public_text(text):return text.replace(str(ROOT),'<project>')
def run(label,argv,cwd,negative=False,diagnostic=''):
 p=subprocess.run(argv,cwd=cwd,env=ENV,capture_output=True,text=True)
 output=p.stdout+p.stderr
 (LOGS/('control-'+label+'.log')).write_text(public_text(output))
 row=dict(name=label,command=[public_text(a) for a in argv],actual_exit=p.returncode,
          negative=negative,expected_diagnostic=diagnostic,
          passed=(p.returncode!=0 and diagnostic in output) if negative else p.returncode==0)
 rows.append(row)
 return row,output

with tempfile.TemporaryDirectory(prefix='controls-',dir=ROOT/'.lake') as temp:
 TEMP=Path(temp)
 helpers=TEMP/'helpers';helpers.mkdir()
 ENV['LEAN_PATH']=str(helpers)+(':'+ENV['LEAN_PATH'] if ENV.get('LEAN_PATH') else '')
 for name in ['NormedMeaningChecks','ExtensionMeaningChecks','MeaningChecks']:
  row,output=run('semantic-'+name,['lake','env','lean','--root='+str(ROOT/'controls'),
                 '-o',str(helpers/(name+'.olean')),str(ROOT/'controls'/(name+'.lean'))],ROOT)
  if not row['passed'] or 'uses `sorry`' in output:raise RuntimeError('Semantic baseline failed: '+name)
 inventory,_=run('compiler-inventory',['lake','env','lean',str(ROOT/'controls/IndependentAudit.lean')],ROOT)
 if not inventory['passed']:raise RuntimeError('Compiler environment audit failed')
 original=(ROOT/'logs/axioms.log').read_text()
 entries=json.loads((ROOT/'exported-theorems.json').read_text())
 new=[e for e in entries if e['source'] in {'Mxym/NormedBalance.lean','Mxym/CofactorNormedBalance.lean'}]
 if len(entries)!=68 or len(new)!=8:raise RuntimeError('Unexpected project inventory')

 def axiom_case(label,text,negative,diagnostic=''):
  p=TEMP/label;(p/'scripts').mkdir(parents=True);(p/'logs').mkdir()
  shutil.copyfile(ROOT/'scripts/check_axioms.py',p/'scripts/check_axioms.py')
  shutil.copyfile(ROOT/'exported-theorems.json',p/'exported-theorems.json')
  (p/'logs/axioms.log').write_text(text)
  return run(label,['python3','scripts/check_axioms.py'],p,negative,diagnostic)
 baseline,_=axiom_case('axiom-baseline',original,False)
 if not baseline['passed']:raise RuntimeError('Axiom baseline failed')
 for idx,item in enumerate(new):
  line=next(s for s in original.splitlines(keepends=True) if s.startswith("'"+item['name']+"'"))
  axiom_case('axiom-missing-'+str(idx+1),original.replace(line,''),True,'Missing or unexpected #print axioms result')
 line=next(s for s in original.splitlines(keepends=True) if s.startswith("'"+new[0]['name']+"'"))
 axiom_case('axiom-duplicate',original+line,True,'Duplicate axiom output')
 axiom_case('axiom-unexpected',original+"'Control.unexpected' depends on axioms: [propext]\n",True,
            'Missing or unexpected #print axioms result')
 for label,ax in [('sorry','sorryAx'),('custom','Control.customAx'),('native','Lean.ofReduceBool')]:
  axiom_case('axiom-'+label,original.replace(line,line.replace(']',', '+ax+']')),True,'Unpermitted axiom')

 def project_case(label):
  p=TEMP/label
  shutil.copytree(ROOT,p,ignore=shutil.ignore_patterns('.lake','.elan','.cache','logs','__pycache__'))
  shutil.copytree(ROOT/'logs',p/'logs',ignore=shutil.ignore_patterns('control-*','controls-summary.json'))
  (p/'.lake').symlink_to(ROOT/'.lake',target_is_directory=True)
  return p
 for label,field,value in [('pin-revision','rev','0'*40),('pin-origin','url','https://example.invalid/unreviewed.git')]:
  p=project_case(label);manifest=p/'lake-manifest.json';data=json.loads(manifest.read_text())
  next(v for v in data['packages'] if v['name']=='mathlib')[field]=value
  manifest.write_text(json.dumps(data,indent=2)+'\n')
  run(label,['python3','scripts/check_pins.py'],p,True,'mathlib: locked source or revision differs from reviewed pin')
 p=project_case('pin-optimized');(p/'lean-toolchain').write_text('leanprover/lean4:v4.0.0\n')
 run('pin-optimized',['python3','-O','scripts/check_pins.py'],p,True,'Toolchain file differs from reviewed pin')

 p=project_case('coverage-signature');f=p/'logs/statements.log';text=f.read_text()
 anchor='Mxym.NormedBalance.coefficient_balance.{u_1, u_2}'
 if text.count(anchor)!=1:raise RuntimeError('Signature anchor not unique')
 f.write_text(text.replace(anchor,anchor+' (falseHyp : False)'))
 run('coverage-signature',['python3','scripts/generate_coverage.py'],p,True,
     'Stored signature log differs from freshly elaborated signatures')
 p=project_case('coverage-axioms')
 (p/'logs/axioms.log').write_text(original.replace(line,line.replace(']',', Control.customAx]')))
 run('coverage-axioms',['python3','scripts/generate_coverage.py'],p,True,'Stored axiom log differs from fresh Lean output')

 p=project_case('protected');f=p/'Mxym/NormedBalance.lean'
 f.write_text(f.read_text().replace('\nend Mxym.NormedBalance',
     '\nprotected theorem inventorySentinel : True := by trivial\n\nend Mxym.NormedBalance'))
 compiled,_=run('protected-compile',['lake','env','lean','Mxym/NormedBalance.lean'],p)
 inventoried,_=run('protected-inventory',['python3','scripts/generate_audit.py'],p)
 exports=json.loads((p/'exported-theorems.json').read_text())
 inventoried['passed']=inventoried['passed'] and compiled['passed'] and len(exports)==69 and any(
     e['name']=='Mxym.NormedBalance.inventorySentinel' for e in exports)
 inventoried['observed_export_count']=len(exports)
 for label,code in [('source-sorry','theorem escape : True := by sorry'),
                    ('source-axiom','axiom escape : False'),
                    ('source-native','theorem escape : True := by native_decide'),
                    ('source-unsafe','unsafe def escape : Nat := 0')]:
  p=project_case(label);f=p/'Mxym/NormedBalance.lean'
  f.write_text(f.read_text().replace('\nend Mxym.NormedBalance','\n'+code+'\n\nend Mxym.NormedBalance'))
  run(label,['python3','scripts/generate_audit.py'],p,True,'Forbidden proof escape')

 cases=[
  ('missing-unit','NormedMeaningChecks','NormedAudit Mxym.Determinant','|oneC 0| ≤ (∑ j, |oneC j|)/2','oneC','refute_missing_unit'),
  ('missing-relation','NormedMeaningChecks','NormedAudit Mxym.Determinant','|oneC 0| ≤ (∑ j, |oneC j|)/2','oneC','refute_missing_relation'),
  ('small-norm','NormedMeaningChecks','NormedAudit Mxym.Determinant','|smallNormC 0| ≤ (∑ j, |smallNormC j|)/2','smallNormC, Fin.sum_univ_succ','refute_norm_le_one'),
  ('nonunit-cofactor','NormedMeaningChecks','NormedAudit Mxym.Determinant','|cofactor nonunitMatrix 1| ≤ (∑ j, |cofactor nonunitMatrix j|)/2','Fin.sum_univ_succ, nonunit_cofactor_zero, nonunit_cofactor_one','refute_nonunit_columns'),
  ('four-witness','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean three','three_mean','refute_no_witness'),
  ('repeated-witness','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean three','three_mean','refute_repeated_witness'),
  ('mass-normalization','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((0 : ℝ)/2) ((0 : ℝ)/4) ≤ 1/2 - mean noMassNormalization','noMassNormalization_mean','refute_no_normalization'),
  ('negative-coefficient','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((0 : ℝ)/2) ((0 : ℝ)/4) ≤ 1/2 - mean negativeCoefficient','negativeCoefficient_mean','refute_negative_coefficient'),
  ('cap-gap','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((1/6 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean falseGap','falseGap_mean','refute_false_gap'),
  ('fourth-bound','ExtensionMeaningChecks','ExtensionAudit Mxym.Rademacher','min ((1/3 : ℝ)/2) ((1/6 : ℝ)/4) ≤ 1/2 - mean falseFourthLowerBound','falseFourthLowerBound_mean','refute_false_fourth_bound')]
 def mathematics(case):
  label,module,opens,proposition,simp,refutation=case
  prefix='import '+module+'\nopen scoped BigOperators\nopen '+opens+'\n'
  valid=TEMP/(label+'-refutation.lean');invalid=TEMP/(label+'-invalid.lean')
  valid.write_text(prefix+'example : ¬ ('+proposition+') := '+refutation+'\n')
  invalid.write_text(prefix+'example : '+proposition+' := by\n  norm_num ['+simp+']\n')
  rv=subprocess.run(['lake','env','lean',str(valid)],cwd=ROOT,env=ENV,capture_output=True,text=True)
  ri=subprocess.run(['lake','env','lean',str(invalid)],cwd=ROOT,env=ENV,capture_output=True,text=True)
  vt=rv.stdout+rv.stderr;it=ri.stdout+ri.stderr
  (LOGS/('control-math-'+label+'-refutation.log')).write_text(public_text(vt))
  (LOGS/('control-math-'+label+'.log')).write_text(public_text(it))
  return dict(name='math-'+label,actual_exit=ri.returncode,refutation_exit=rv.returncode,negative=True,
      passed=rv.returncode==0 and ri.returncode!=0 and 'unsolved goals' in it and '⊢ False' in it and 'uses `sorry`' not in vt)
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:rows.extend(pool.map(mathematics,cases))
 negative=[r for r in rows if r['negative']]
 report=dict(negative_checks=len(negative),negative_passed=sum(r['passed'] for r in negative),
             positive_checks=len(rows)-len(negative),failed=[r['name'] for r in rows if not r['passed']],controls=rows)
 (LOGS/'controls-summary.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='controls'}))
 if report['failed'] or len(negative)!=32:raise SystemExit(1)
