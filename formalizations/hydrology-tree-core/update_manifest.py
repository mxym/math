#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parent
modules=['HydrologyTree.Coefficients','HydrologyTree.LeadingCoefficients','HydrologyTree.BlockJacobian','HydrologyTree.Scaling','HydrologyTree.Triangular','HydrologyTree.Gluing','HydrologyTree.RootUpdate','HydrologyTree.RateChart','HydrologyTree.CompartmentMatrix','HydrologyTree.PhysicalBridge','HydrologyTree.Resolvent','HydrologyTree.EdgeDeterminant','HydrologyTree.EdgeCharacteristic','HydrologyTree.RootAttachment','HydrologyTree.BranchAssembly','HydrologyTree.LeafRecursion','HydrologyTree.PhysicalLeaf','HydrologyTree.ProductDerivative','HydrologyTree.JacobianComposition','HydrologyTree.FamilyProduct','HydrologyTree.FamilyResultants','HydrologyTree.FamilySmoothness','HydrologyTree.TangentJacobian','HydrologyTree.FamilyGluing','HydrologyTree']
(ROOT/'MODULES.json').write_text(json.dumps(modules,indent=2)+'\n')
roots=[]
for module in modules:
 text=(ROOT/(module.replace('.','/')+'.lean')).read_text()
 roots += ['HydrologyTree.'+x for x in re.findall(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma|def|abbrev|instance|structure)\s+(\w+)', text)]
(ROOT/'ROOTS.txt').write_text('\n'.join(roots)+'\n')
(ROOT/'audit/Audit.lean').write_text('import HydrologyTree\n\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
p=ROOT/'audit/Replay.lean'
s=p.read_text();a=s.index('  let roots := [');b=s.index('\n  let cs ',a)
s=s[:a]+'  let roots := [\n    '+',\n    '.join('``'+r for r in roots)+']'+s[b:];p.write_text(s)
files=[m.replace('.','/')+'.lean' for m in modules]+['audit/Audit.lean','audit/Replay.lean','MODULES.json','ROOTS.txt','lakefile.toml','lake-manifest.json','lean-toolchain','reproduce.py','update_manifest.py','fetch_cache.sh']
(ROOT/'SOURCE_SHA256.json').write_text(json.dumps({f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in sorted(files)},indent=2)+'\n')
print('modules',len(modules),'roots',len(roots))
