"""Exact computer-assisted six-point disk bound. No cached coefficients.
Requires Python 3.9+, NumPy, C++17, and GMP with 64-bit unsigned long.
"""
from collections import defaultdict
from itertools import product, combinations_with_replacement
from pathlib import Path
import subprocess,tempfile
import numpy as np
from lower_exact import values, grid, interpolate, require

def main():
    pts=grid(); require(len(pts)==3876,'wrong gap grid')
    base=values([1]*5); K=sorted(base); labels=[0,1,2,3,4,5,8,9,10,11]
    require(K==list(combinations_with_replacement(labels,4)),'support mismatch')
    v=np.empty((len(pts),len(K)),dtype=object)
    for q,p in enumerate(pts):
        z=values([1+x for x in p]+[1]);require(z.keys()==base.keys(),'missing or new term')
        v[q]=[z[k] for k in K]
    interpolate(pts,v);require(np.array_equal(v.sum(axis=0),[base[k] for k in K]),'at-one check')
    # A=S*D*F. First get H=- (d/du_i-d/dv_i)(d/du_j-d/dv_j) A.
    # Keep both ordered derivatives. The rules are integer linear maps on v.
    HH=defaultdict(lambda:defaultdict(int))
    for q,k in enumerate(K):
        for a,i in enumerate(k):
            if i<2:continue
            for b,j in enumerate(k):
                if a==b or j<2:continue
                rem=tuple(r for c,r in enumerate(k) if c not in (a,b))
                HH[rem,(i-2)%6,(j-2)%6][q]+= -1 if (i>=8)==(j>=8) else 1
    f0=lambda r:r if r<2 else 2+(r-2)%6
    # C(w,s)=H(w,u=s,v=s), and B=4[5C(w,(u+v)/2)+H(w,u,v)].
    C=defaultdict(lambda:defaultdict(int))
    B=defaultdict(lambda:defaultdict(int))
    for (k,i,j),terms in HH.items():
        ck=tuple(sorted(map(f0,k))); e=sum(r>=2 for r in ck)
        for q,w in terms.items():
            C[ck,i,j][q]+=w
            B[k,i,j][q]+=4*w
            for bits in product((0,1),repeat=e):
                it=iter(bits); mk=tuple(sorted(r if r<2 else r+6*next(it) for r in ck))
                B[mk,i,j][q]+=(20//(2**e))*w
    # Tasks: all 21 monomial matrices of C; the four strong same-half
    # B coefficients (two node pairs, either relative color); the eight
    # crossed two-color binary quadratics. Exchange the two color labels
    # simultaneously: B is invariant, also verified at the rule level.
    def entries(table,k):
        M={}
        for i in range(4):
            for j in range(i,4):
                rule={a:b for a,b in table[k,i,j].items() if b}
                require(rule=={a:b for a,b in table[k,j,i].items() if b},'nonsymmetric Hessian')
                ar=np.zeros(len(pts),dtype=object)
                for a,b in rule.items():ar+=b*v[:,a]
                M[i,j]=ar
        return M
    def opposite(k):return tuple(sorted(r if r<2 else r+6 if r<6 else r-6 for r in k))
    def bcm(k):
        k=tuple(sorted(k))
        if k not in bcm.cache:
            M=entries(B,k);R=entries(B,opposite(k))
            require(all(np.array_equal(M[q],R[q]) for q in M),'color reflection')
            bcm.cache[k]=M
        return bcm.cache[k]
    bcm.cache={}
    tasks=[]
    for k in combinations_with_replacement(range(6),2):tasks.append((f'C{k[0]}{k[1]}',13+sum(r>=2 for r in k),[entries(C,k)]))
    for i,j in [(2,3),(4,5)]:
        for t in (0,6):tasks.append((f'B{i}_{j+t}',15,[bcm((i,j+t))]))
    for i,j in product((2,3),(4,5)):
        for t in (0,6):
            cross=bcm((i,j+t));tasks.append((f'P{i}_{j+t}',15,[bcm((i,i)),{q:2*a for q,a in cross.items()},bcm((j,j))]))
    require(len(tasks)==33,'incomplete tasks')
    root=Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as td:
        t=Path(td);p=t/'coefficients'
        with p.open('w') as f:
            print(len(tasks),file=f)
            for tag,deg,matrices in tasks:
                print(tag,deg,len(matrices),file=f)
                for M in matrices:
                    for i in range(4):
                        for j in range(i,4):
                            ar=M[i,j];nz=np.flatnonzero(ar);print(len(nz),file=f)
                            for h in nz:
                                v0=pts[h];last=deg-sum(v0);require(last>=0 and type(ar[h]) is int,'bad entry coefficient')
                                print(*v0,last,ar[h],file=f)
        subprocess.run(['g++','-std=c++17','-O2',str(root/'upper_pack.cpp'),'-lgmpxx','-lgmp','-o',str(t/'verify')],check=True)
        subprocess.run([str(t/'verify'),str(p)],check=True)
if __name__=='__main__':main()
