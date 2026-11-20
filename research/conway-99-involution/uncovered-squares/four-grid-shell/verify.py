if not __debug__:
    raise RuntimeError("Run without python -O; proof assertions must remain enabled.")

from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess,sys
from check_integer import run
import json
from double4 import dsolve
p=Path(__file__).resolve().parent
data=json.loads((p/'integer.json').read_text());assert set(data)=={'42991782400','45141371392'}
for code,r in data.items():run(int(code),r)
with TemporaryDirectory()as tmp:
 t=Path(tmp);D=dsolve();assert len(D)==21
 (t/'double.dat').write_text(''.join(' '.join(str(sum(v*6**i for i,v in enumerate(w)))for w in g)+'\n'for g in D))
 for s in ['exact4','exact41']:subprocess.run(['g++','-O3','-std=c++17',str(p/(s+'.cpp')),'-o',str(t/s)],check=True)
 from norm41 import out
 assert out==[(0,16),(2,16),(3,16)]
 run2=lambda *args:subprocess.check_output([str(t/args[0]),*(str(x)for x in args[1:])],cwd=t,text=True).splitlines()
 A=[list(map(int,s.split()))for s in run2('exact4')];assert [s[:2]for s in A]==[[i,0]for i in range(21)];assert A==[list(map(int,z.split()))for z in (p/'frames002.tsv').read_text().splitlines()];print('002:',len(A),'frames,',sum(a[2]for a in A),'search nodes, none feasible.',flush=True)
 for j,_ in out:
  U=[list(map(int,s.split()))for s in run2('exact41',j)];assert len(U)==1 and U[0][:2]==[j,0];print('011 frame',j,'nodes',U[0][2],'none feasible.',flush=True)
