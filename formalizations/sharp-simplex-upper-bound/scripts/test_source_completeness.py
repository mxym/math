#!/usr/bin/env python3
"""Exercise the exact production recursive source scanner, including cached missing sources.
Synthetic fixtures isolate failure causes; never modify real dependency checkouts.
"""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
PROGRAM="""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,sys.argv[1])
import source_inventory as si
r=Path(sys.argv[2]);si.root_sources=lambda _: {'Entry005':r/'formal/Entry005.lean'}
try:
 g=si.closure(r/'formal',r/'packages',r/'core',['mock'])
 print('SOURCE_CLOSURE_PASS',len(g))
except RuntimeError as e:
 print('SOURCE_CLOSURE_REJECT',str(e));sys.exit(7)
"""
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 snap=validated_snapshot(ROOT);require(not a.output.resolve().is_relative_to(ROOT),'write report outside release');rows=[]
 cases=['complete_source','missing_nonofficial_source_cache_exists','missing_transitive_nonofficial_source_cache_exists','ambiguous_source_providers','missing_implicit_Init_source_cache_exists']
 for case in cases:
  with tempfile.TemporaryDirectory(prefix='upper-source-control-') as td:
   r=Path(td)
   for n,t in {'formal/Entry005.lean':'import Mock.Helper\n','packages/mock/Mock/Helper.lean':'import Mock.Transitive\n','packages/mock/Mock/Transitive.lean':'def testValue : Nat := 1\n','core/Init.lean':'prelude\n'}.items():
    f=r/n;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(t)
   cache=r/'packages/mock/.lake/build/lib/lean/Mock';cache.mkdir(parents=True)
   (cache/'Helper.olean').write_bytes(b'cached object must not satisfy source completeness')
   (cache/'Transitive.olean').write_bytes(b'cached object must not satisfy source completeness')
   (r/'core/Init.olean').write_bytes(b'cache is not source')
   target=None
   if case=='missing_nonofficial_source_cache_exists':target=r/'packages/mock/Mock/Helper.lean'
   if case=='missing_transitive_nonofficial_source_cache_exists':target=r/'packages/mock/Mock/Transitive.lean'
   if case=='missing_implicit_Init_source_cache_exists':target=r/'core/Init.lean'
   if target:target.unlink()
   if case=='ambiguous_source_providers':
    p=r/'formal/Mock/Helper.lean';p.parent.mkdir();p.write_text('def other : Nat := 0\n')
   for opt in [False,True]:
    p=subprocess.run([sys.executable,*(['-O'] if opt else []),'-B','-c',PROGRAM,str(ROOT/'scripts'),str(r)],capture_output=True,text=True)
    expected=case=='complete_source'
    require((p.returncode==0 and 'SOURCE_CLOSURE_PASS' in p.stdout) if expected else (p.returncode==7 and 'Expected one source for ' in p.stdout),'source completeness control failed '+case+' '+p.stdout+p.stderr)
    rows.append({'case':case,'optimized':opt,'cache_exists':True,'expected':'accept' if expected else 'reject_missing_or_ambiguous_source','passed':True})
 require(validated_snapshot(ROOT)==snap,'release mutated by source controls')
 a.output.write_text(json.dumps({'status':'PASS','scope':'Exact production recursive source resolver, synthetic dependency-source omission/cache-presence controls','normal_and_optimized':True,'results':rows},indent=2)+'\n');print('SOURCE_COMPLETENESS_CONTROLS_PASS',len(rows))
if __name__=='__main__':
 try:main()
 except (ReleaseIntegrityError,OSError,ValueError) as e:print(str(e),file=sys.stderr);sys.exit(1)
