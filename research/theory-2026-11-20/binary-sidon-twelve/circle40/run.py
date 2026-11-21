"""Construct the circle from its field, cover all directions, and exhaust both 26-layer searches."""
from pathlib import Path
from itertools import combinations
from collections import Counter
from tempfile import TemporaryDirectory
import subprocess,os,sys
root=Path(__file__).resolve().parent
def insist(condition, reason):
    if not condition:raise ValueError(reason)
def base(x,y):
    result=0
    while y:
        if y&1:result^=x
        x<<=1
        if x&64:x^=67
        y>>=1
    return result
def pw(x,n,times):
    v=1
    while n:
        if n&1:v=times(v,x)
        n>>=1;x=times(x,x)
    return v
insist(all(pw(x,63,base)==1 for x in range(1,64)),"base field")
def tr(x):
    a=x;o=0
    for i in range(6):o^=a;a=base(a,a)
    return o
delta=next(x for x in range(64)if tr(x)==1)
def mul(x,y):
    a,b=x%64,x//64;c,d=y%64,y//64
    bd=base(b,d)
    return (base(a,c)^base(delta,bd))+64*(base(a,d)^base(b,c)^bd)
def sidon(a):
    return len(a)==len(set(a)) and len({x^y for x,y in combinations(a,2)})==len(a)*(len(a)-1)//2
def canonical(B):
    return min(sorted(x^t for x in B)for t in B)
S=[0]+[x for x in range(1,4096)if pw(x,65,mul)==1]
insist(len(S)==66 and sidon(S),"norm circle + nucleus")
alpha=next(x for x in S[1:]if pw(x,13,mul)!=1 and pw(x,5,mul)!=1)
def dot(x,y):return (x&y).bit_count()&1
def value(mat,x):
    v=0
    for i in range(12):
        if x>>i&1:v^=mat[i]
    return v
def transpose(mat,u):
    return sum(dot(c,u)<<i for i,c in enumerate(mat))
mats=[]
for op in [lambda x:mul(alpha,x),lambda x:mul(x,x)]:
    mat=[op(1<<i)for i in range(12)]
    insist(len({op(x)for x in range(4096)})==4096 and {op(x)for x in S}==set(S) and all(op(x)==value(mat,x)for x in range(4096)),"generator")
    mats.append(mat)
print("GF(64) delta",delta,"norm-one generator",alpha,"linear columns",mats,flush=True)
V=set(range(1,4096));sections=[];mass=Counter()
while V:
    u=min(V);Q=[u];V.remove(u)
    for v in Q:
        for mat in mats:
            z=transpose(mat,v)
            if z in V:Q.append(z);V.remove(z)
    ws={sum(1-2*dot(t,x)for x in S)for t in Q}
    insist(len(ws)==1,"constant signed character in orbit");w=ws.pop();mass[w]+=len(Q)
    if abs(w)==14:
        j=(u&-u).bit_length()-1
        def fold(x):return (x&((1<<j)-1))|((x>>(j+1))<<j)
        a=[fold(x)for x in S if dot(u,x)==int(w<0)]
        b=[fold(x)for x in S if dot(u,x)!=int(w<0)]
        insist(len(a)==40 and len(b)==26 and sidon(a+[x+2048 for x in b]),"plant")
        insist(len(set(a)|{x^y^z for x,y,z in combinations(a,3)})==2048,"maximality")
        span={0}
        for x in a:span|={v^x^a[0]for v in span}
        insist(len(span)==2048,"affine span")
        sections.append((u,w,len(Q),a,b))
insist(dict(mass)=={2:780,6:780,-6:585,-10:520,10:455,-2:390,14:390,-14:195},"all 4095 directions")
insist([(u,w,n)for u,w,n,a,b in sections]==[(6,14,390),(17,-14,195)],"two orbits")
for idx,desc in enumerate(sections):
    u,w,n,a,b=desc
    text=(root/'sections.txt').read_text().splitlines()[2*idx:2*idx+2]
    insist(set(a)==set(map(int,text[0].split())) and set(b)==set(map(int,text[1].split())),"stored anchors")
print("Walsh distribution",sorted(mass.items()),"sections",[(u,w,n)for u,w,n,a,b in sections],flush=True)
with TemporaryDirectory()as wd:
    for eng in ['degree','numeric']:
        exe=Path(wd)/eng
        subprocess.run([os.environ.get('CXX','g++'),'-O3','-march=native','-std=c++17',str(root/f'search_{eng}.cpp'),'-o',str(exe)],check=True)
        for u,w,n,a,b in sections:
            r=subprocess.run([str(exe),'26'],input=' '.join(map(str,a))+'\n',text=True,capture_output=True,check=True)
            print(eng,'normal',u,r.stderr.strip(),flush=True)
            lines=r.stdout.splitlines()
            insist(len(lines)==16 and [int(s.split()[1])for s in lines[:14]]==list(range(13,27)) and all(s.startswith('k ')for s in lines[:14]),"entire k interval")
            insist(lines[-2].startswith('B ') and list(map(int,lines[-2].split()[1:]))==canonical(b) and lines[-1]=='TOTAL 1',"entire translate class")
            print(r.stdout.strip(),flush=True)
print("PASS. Both maximum-section orbits have precisely their planted opposite 26-set up to translation.",flush=True)
