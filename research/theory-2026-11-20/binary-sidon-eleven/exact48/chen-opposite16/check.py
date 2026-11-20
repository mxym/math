from pathlib import Path
from itertools import combinations
from collections import Counter
import subprocess,sys,tempfile
from apn import truth
root=Path(__file__).resolve().parent
def ck(a,msg):
    if not a:raise ValueError(msg)
def run(cmd,inp):
    p=subprocess.run(cmd,input=inp,text=True,capture_output=True,check=True)
    return p.stdout.rstrip().splitlines()
def check():
    a=(root/'chen48.txt').read_text();A=list(map(int,a.split()))
    ck(len(set(A))==len(A)==48 and all(0<=a<2048 for a in A),'input 48')
    with tempfile.TemporaryDirectory()as tmp:
        for src in ['pair','root']:
            subprocess.run(['g++','-std=c++17','-O3','-DWIDTH=16',str(root/(src+'.cpp')),'-o',str(Path(tmp)/src)],check=True)
        r1=run([str(Path(tmp)/'pair'),'16'],a);r2=run([str(Path(tmp)/'root'),'16','2048','1','32'],a)
    ck(len(r1)==2 and r1[-1].startswith('hit 0 nodes '),'pair enumeration')
    ck(len(r2)==2 and r2[-1]=='16','root enumeration')
    B=list(map(int,r1[0].split()));V=list(map(int,r2[0].split()))
    ck(V[:48]==A,'root anchor')
    D={x-2048 for x in V[48:]};ck(any({x^y for x in B}==D for y in B),'distinct enumerations')
    ck(len(set(B))==len(B)==16 and all(0<=b<2048 for b in B),'B size')
    S=set(A)|{2048^b for b in B}
    ps=lambda w:{x^y for x,y in combinations(w,2)}
    ck(len(S)==64 and len(ps(S))==2016,'Sidon witness')
    ck(not(ps(A)&ps(B)),'disjoint differences')
    f=truth();G={x+64*y for x,y in enumerate(f)};ck(len(G)==64,'graph size')
    for h in range(1,64):ck(all(v==2 for v in Counter(f[x]^f[x^h]for x in range(64)).values()),'APN derivatives')
    L=max(abs(sum(1-2*(((a&x).bit_count()+(b&f[x]).bit_count())%2)for x in range(64)))for a in range(64)for b in range(1,64))
    ck(L==32,'Walsh linearity')
    m,p=(root/'linear_map.txt').read_text().splitlines()
    M=list(map(int,m.split()));p,q=map(int,p.split())
    def T(x):
        y=q;x^=p
        for j,v in enumerate(M):
            if x>>j&1:y^=v
        return y
    ck(len(M)==12 and len({T(x)for x in range(4096)})==4096,'invertibility')
    ck({T(x)for x in G}==S,'exact affine graph map')
    print('PASS: 1 least-difference representative; 16 labeled rooted examples giving 1 translation orbit. Gold-extension graph APN, Walsh linearity 32, explicit invertible binary map checked.')
if __name__=='__main__':check()
