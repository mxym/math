#!/usr/bin/env python3
"""Replay deliberate corruptions against original and locally hardened checkers.

Read original checker bytes with git show at the pinned commit. Substitute only
in-memory JSON reads; no shipped certificate or inherited source is changed.
Run this script with both python3 and python3 -O.
"""
import argparse
import contextlib
import copy
import io
import json
import subprocess
import types
from pathlib import Path

PIN='87868bcb65bf0460a90d6bc2efc3324e46481230'
ENTRY='preprints/002-quadratic-order-moats'

def module(repo,script,original,original_tree=None):
    p=repo/ENTRY/'v4/code'/script
    if original and original_tree is not None:
        source=(original_tree/ENTRY/'v4/code'/script).read_text()
    elif original:
        source=subprocess.check_output(['git','show',PIN+':'+str(p.relative_to(repo))],cwd=repo,text=True)
    else:source=p.read_text()
    m=types.ModuleType('audit_target');m.__file__=str(p)
    exec(compile(source,str(p),'exec'),m.__dict__)
    return m

def run(m,substitutions):
    read=Path.read_text
    def replaced(path,*args,**kw):
        if path.name in substitutions:return json.dumps(substitutions[path.name])
        return read(path,*args,**kw)
    Path.read_text=replaced
    try:
        with contextlib.redirect_stdout(io.StringIO()):m.main()
        return {'accepts':True}
    except (ValueError,ArithmeticError,KeyError,TypeError,IndexError) as e:
        return {'accepts':False,'exception':type(e).__name__,'message':str(e)}
    finally:Path.read_text=read

def main():
    p=argparse.ArgumentParser();p.add_argument('repo',type=Path);p.add_argument('--output',type=Path);p.add_argument('--original-tree',type=Path);args=p.parse_args()
    repo=args.repo.resolve();code=repo/ENTRY/'v4/code';v3=repo/ENTRY/'v3/certificates_v3'
    load=lambda name:json.loads((code/name).read_text())
    g=load('period_optimality.json');e=load('endpoint_rigidity.json');r=load('sqrt2_period_endpoint.json')
    gb=json.loads((v3/'gaussian_eight_steps_principal.json').read_text());rb=json.loads((v3/'sqrt2_eight_steps.json').read_text())
    controls=[]
    def add(name,script,replacements,original_accepts):controls.append((name,script,replacements,original_accepts))
    bad=copy.deepcopy(r)
    for c in bad['failed_prime_subsets']:
        c['generators']=[];c['witness']={'root':[0,0],'steps':[[1,0]]*14,'voltage':[1,0],'allowed_residues':196}
    add('sqrt2 labelled subset replaced by empty sieve','check_sqrt2_period.py',{'sqrt2_period_endpoint.json':bad},True)
    bad=copy.deepcopy(rb);bad['data']['steps']=[[-1,0],[0,-1],[0,1],[1,0]]
    add('sqrt2 positive F8 replaced by F4','check_sqrt2_period.py',{'sqrt2_eight_steps.json':bad},True)
    bad=copy.deepcopy(g);bad['positive_generators'].append([1,1]);bundle=copy.deepcopy(gb);bundle['data']['generators'].append({'alpha':[1,1]})
    add('Gaussian endpoint changed to six generators','check_period_optimality.py',{'period_optimality.json':bad,'gaussian_eight_steps_principal.json':bundle},True)
    for name,script,data,case in [('Gaussian lower','check_period_optimality.py',g,'failed_radicals'),('Gaussian rigidity','check_endpoint_rigidity.py',e,'proper_prime_subset_failures'),('sqrt2 lower','check_sqrt2_period.py',r,'lower_period_failures')]:
        filename={'Gaussian lower':'period_optimality.json','Gaussian rigidity':'endpoint_rigidity.json','sqrt2 lower':'sqrt2_period_endpoint.json'}[name]
        bad=copy.deepcopy(data);w=bad[case][0] if name=='Gaussian lower' else bad[case][0]['witness'];w['root'][0]=float(w['root'][0])
        add(name+' accepts floating root',script,{filename:bad},True)
        bad=copy.deepcopy(data);w=bad[case][0] if name=='Gaussian lower' else bad[case][0]['witness'];w['voltage']=[0,0]
        add(name+' zero stored voltage',script,{filename:bad},False)
        bad=copy.deepcopy(data);bad[case].pop()
        add(name+' missing case',script,{filename:bad},False)
        bad=copy.deepcopy(data);w=bad[case][0] if name=='Gaussian lower' else bad[case][0]['witness'];w['steps'][0]=[2,0]
        add(name+' non-F8 step',script,{filename:bad},False)
    for label,bundle,file,script in [('Gaussian',gb,'gaussian_eight_steps_principal.json','check_period_optimality.py'),('sqrt2',rb,'sqrt2_eight_steps.json','check_sqrt2_period.py')]:
        bad=copy.deepcopy(bundle);bad['certificate']['potentials'][0][2]+=1
        add(label+' altered endpoint potential',script,{file:bad},False)
        bad=copy.deepcopy(bundle);bad['certificate']['potentials'].pop()
        add(label+' missing endpoint residue',script,{file:bad},False)
    rows=[]
    for name,script,replacements,expected in controls:
        answers={label:run(module(repo,script,original,args.original_tree),replacements) for label,original in [('original',True),('fixed',False)]}
        if answers['original']['accepts']!=expected or answers['fixed']['accepts']:
            raise RuntimeError('unexpected control outcome: '+name+' '+str(answers))
        rows.append(dict(control=name,**answers))
    result=dict(status='PASS',controls=len(rows),original_acceptance_gaps=sum(x['original']['accepts'] for x in rows),all_fixed_reject=True,results=rows)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
