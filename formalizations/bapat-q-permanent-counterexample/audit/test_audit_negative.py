#!/usr/bin/env python3
"""Mutation controls for audit_bundle.py; use python or python -O."""
import argparse,gzip,json,shutil,tempfile
from pathlib import Path
from audit_bundle import dependencies,integers,check

def write(p,obj):
 b=json.dumps(obj).encode();p.write_bytes(gzip.compress(b,mtime=0) if p.suffix=='.gz' else b)
def run(root):
 with tempfile.TemporaryDirectory(prefix='bapat-audit-negative-') as td:
  c=Path(td)/'compact';shutil.copytree(root,c);m=c/'fresh-verification/manifest';results=[]
  def trial(name,path,mutation,fn):
   data=path.read_bytes()
   try:
    mutation(path)
    try:fn(c)
    except ValueError as e:results.append({'test':name,'rejected':True,'reason':str(e)})
    else:raise RuntimeError('MUTATION NOT REJECTED: '+name)
   finally:path.write_bytes(data)
  graph=m/'all-owned-closure.json.gz'
  def graphchange(fn):
   def f(p):
    obj=json.loads(gzip.decompress(p.read_bytes()));fn(obj);write(p,obj)
   return f
  trial('missing closure node',graph,graphchange(lambda x:x.pop()),dependencies)
  trial('unsafe closure declaration',graph,graphchange(lambda x:x[0].update(unsafe=True)),dependencies)
  trial('partial closure declaration',graph,graphchange(lambda x:x[0].update(partial=True)),dependencies)
  trial('unexpected axiom',graph,graphchange(lambda x:x[0].update(kind='axiom')),dependencies)
  trial('duplicate graph declaration',graph,graphchange(lambda x:x.append(x[0])),dependencies)
  roots=m/'requested-root-closure.json.gz'
  trial('truncated root closure',roots,lambda p:write(p,json.loads(gzip.decompress(p.read_bytes()))[:-1]),dependencies)
  inv=m/'owned-inventory.json.gz'
  def bad_axiom(p):
   a=json.loads(gzip.decompress(p.read_bytes()));a[0]['axioms']=[];write(p,a)
  trial('forged inventory axiom set',inv,bad_axiom,dependencies)
  csv=c/'formalization/reference/counterexample_vectors_n200.csv'
  trial('CSV coordinate mutation',csv,lambda p:p.write_bytes(p.read_bytes().replace(b'13,-5',b'14,-5',1)),integers)
  tr=c/'formalization/sources/BapatN200Trace0.lean'
  trial('checkpoint integer mutation',tr,lambda p:p.write_text(p.read_text().replace('⟨126, -138⟩','⟨127, -138⟩',1)),integers)
  ex=c/'formalization/reference/expected_values.json'
  def bad_norm(p):
   a=json.loads(p.read_bytes());a['permanent']=str(int(a['permanent'])+1);write(p,a)
  trial('expected norm mutation',ex,bad_norm,integers)
  check(len(results)==10 and all(x['rejected'] for x in results),'negative test count')
  return {'status':'PASS','tests':results}
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('compact',type=Path);ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=run(args.compact);args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
