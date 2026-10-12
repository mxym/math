#!/usr/bin/env python3
"""Normal/-O tests of the production source resolver; cached objects never replace source."""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
PROGRAM='''from pathlib import Path
import sys
sys.path.insert(0,sys.argv[1])
import source_inventory as si
r=Path(sys.argv[2]);si.owned_sources=lambda _: {'Entry002':r/'project/lean/Entry002.lean'}
try:
 g=si.closure(r/'project',r/'packages',r/'core',['mock'],[])
 print('SOURCE_CLOSURE_PASS',len(g))
except RuntimeError as e:
 print('SOURCE_CLOSURE_REJECT',e);sys.exit(7)
'''
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();s=validated_snapshot(ROOT)
    require(not a.output.resolve().is_relative_to(ROOT),'report must be outside release');rows=[]
    cases=['complete_source','missing_source_with_cache','missing_transitive_with_cache','missing_Init_with_cache','ambiguous_source','malformed_import']
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='quadratic-source-control-') as td:
            r=Path(td)
            initial={'project/lean/Entry002.lean':'/- nested /- import Bogus -/ comment -/\nimport Mock.Helper Mock.Other\n','packages/mock/Mock/Helper.lean':'import Mock.Transitive\n','packages/mock/Mock/Other.lean':'def other : Nat := 2\n','packages/mock/Mock/Transitive.lean':'def value : Nat := 1\n','core/Init.lean':'prelude\n','core/Lean.lean':'import Init\n','core/Lean/Replay.lean':'import Lean\n','core/Init/Data/Nat/Lemmas.lean':'import Init\n'}
            for n,t in initial.items():p=r/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
            for n in ['Mock/Helper','Mock/Transitive','Init']:
                p=r/'packages/mock/.lake/build/lib/lean'/(n+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'cache is not source')
            missing={'missing_source_with_cache':'packages/mock/Mock/Helper.lean','missing_transitive_with_cache':'packages/mock/Mock/Transitive.lean','missing_Init_with_cache':'core/Init.lean'}
            if case in missing:(r/missing[case]).unlink()
            if case=='ambiguous_source':p=r/'project/lean/Mock/Helper.lean';p.parent.mkdir(parents=True);p.write_text('def duplicate : Nat := 1\n')
            if case=='malformed_import':(r/'packages/mock/Mock/Helper.lean').write_text('import Bad; token\n')
            for opt in [False,True]:
                p=subprocess.run([sys.executable,*(['-O'] if opt else []),'-B','-c',PROGRAM,str(ROOT/'scripts'),str(r)],text=True,capture_output=True)
                good=(p.returncode==0 and 'SOURCE_CLOSURE_PASS' in p.stdout) if case=='complete_source' else p.returncode==7 and 'SOURCE_CLOSURE_REJECT' in p.stdout
                require(good,'source resolver control failed '+case+' '+p.stdout+p.stderr);rows.append({'case':case,'optimized':opt,'passed':True})
    require(validated_snapshot(ROOT)==s,'source test changed package');a.output.write_text(json.dumps({'status':'PASS','scope':'Synthetic controls of production recursive source resolver only','results':rows},indent=2)+'\n');print('SOURCE_COMPLETENESS_CONTROLS_PASS',len(rows))
if __name__=='__main__':
    try:main()
    except (ReleaseIntegrityError,OSError,ValueError) as e:print(str(e),file=sys.stderr);sys.exit(1)
