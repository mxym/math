"""Independent finite geometry and direct Gaussian-integer Born rule; no author-module imports."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import sys
import numpy as np
def demand(ok,label):
    if not ok: raise RuntimeError(label)
REPS=[(0,1,2,4,8),(0,1,2,3,4,8),(0,1,2,4,8,15),(0,1,2,3,4,5,8),(0,1,2,3,4,8,12),(0,1,2,3,4,5,6,8),(0,1,2,3,4,5,8,9),(0,1,2,3,4,5,8,10)]
def linspan(vectors):
    s={0}
    for a in vectors:s|={b^a for b in s}
    return s
def orbitcheck():
    generators=[tuple(x^1 for x in range(16))]
    generators += [tuple(x^((1<<i) if x&(1<<j) else 0) for x in range(16)) for i in range(4) for j in range(4) if i!=j]
    # Elementary transvections generate GL; their conjugates of translation by e1 generate all translations.
    def mask(points):return sum(1<<x for x in points)
    maps=[([mask(g[x] for x in range(8) if a>>x&1) for a in range(256)], [mask(g[x+8] for x in range(8) if a>>x&1) for a in range(256)]) for g in generators]
    used=set(); sizes=[]
    for points in REPS:
        m=mask(points);queue=[m];demand(m not in used,"overlapping orbits");used.add(m)
        for p in queue:
            for lo,hi in maps:
                n=lo[p&255]|hi[p>>8]
                if n not in used:used.add(n);queue.append(n)
        sizes.append(len(queue))
    target={mask(c) for h in range(5,9) for c in combinations(range(16),h) if len(linspan(x^c[0] for x in c))==16}
    demand(used==target,"full-span orbit coverage");print("AGL-orbit sizes",sizes)
def make_bases():
    # Parametrize a Lagrangian by its X-projection U and the induced symmetric form on U.
    # Build stabilizer eigenstates as chirps on the cosets of U.
    sub={tuple(sorted(linspan(C))) for r in range(5) for C in combinations(range(1,16),r)}
    demand(len(sub)==67,"subspaces")
    allE=[];allR=[];allI=[];sizes=[];enc=set()
    for U in sorted(sub):
        G=[]
        for x in U:
            if x not in linspan(G):G.append(x)
        r=len(G);q=1<<r
        coord=[0]
        for g in G:coord += [v^g for v in coord]
        coset=sorted({min(x^v for v in U) for x in range(16)})
        dots=[sum((((b&g).bit_count()%2)<<j) for j,g in enumerate(G)) for b in range(16)]
        pairs=list(combinations(range(r),2))
        for diag in range(q):
            for off in range(1<<len(pairs)):
                M=[(diag&(1<<i)) for i in range(r)]
                for j,(k,l) in enumerate(pairs):
                    if off>>j&1:M[k]|=1<<l;M[l]|=1<<k
                E=[];chirp=[]
                for t,a in enumerate(coord):
                    Mt=sum((((m&t).bit_count()%2)<<i) for i,m in enumerate(M))
                    E.extend(a+16*b for b in range(16) if dots[b]==Mt)
                    chirp.append(((diag&t).bit_count()+2*sum(1 for j,(k,l) in enumerate(pairs) if off>>j&1 and t>>k&1 and t>>l&1))%4)
                demand(len(E)==16 and 0 in E and tuple(sorted(E)) not in enc,'bad context')
                enc.add(tuple(sorted(E)));allE.append([a for a in E if a])
                R=np.zeros((16,16),np.int16);I=R.copy()
                for k,c in enumerate(coset):
                    for d in range(q):
                        for t,a in enumerate(coord):
                            s=(-chirp[t]+2*(d&t).bit_count())%4
                            R[k*q+d,c^a]=(1,0,-1,0)[s];I[k*q+d,c^a]=(0,1,0,-1)[s]
                # Orthogonality and joint diagonalization checked in integer arithmetic.
                demand(np.array_equal(R@R.T+I@I.T,q*np.eye(16,dtype=np.int16)) and not np.any(I@R.T-R@I.T),'orthogonality')
                block={0}
                for label in E:
                    if label in block:continue
                    block|={j^label for j in block}
                    a,b=label%16,label//16
                    sign=np.array([1-2*((b&x).bit_count()%2) for x in range(16)],dtype=np.int16)
                    perm=np.arange(16)^a
                    C,T=R[:,perm]*sign,I[:,perm]*sign
                    if (a&b).bit_count()%2:C,T=-T,C
                    equal=np.all((C==R)&(T==I),axis=1)
                    opposite=np.all((C==-R)&(T==-I),axis=1)
                    demand(np.all(equal|opposite),'chirps not joint eigenbras')
                demand(len(block)==16,'spanning labels')
                allR.append(R);allI.append(I);sizes.append(q)
    return np.array(allE),np.asarray(allR),np.asarray(allI),np.asarray(sizes)
def run(path):
    orbitcheck();E,R,I,Q=make_bases()
    demand(len(E)==2295 and np.all(np.bincount(E.ravel())[1:]==135),'context count')
    lines=Path(path).read_text().strip().splitlines();seen=set();depths=Counter();rows=Counter()
    for line in lines:
        row,*codes=map(int,line.split());demand(0<=row<len(REPS),'bad row');S=REPS[row];h=len(S)
        demand(len(codes)==h and all(16<=k<=19 for k in codes),'bad code')
        key=(row,*codes);demand(key not in seen,'duplicate');seen.add(key)
        v=np.zeros(16,np.int16);w=v.copy()
        for x,k in zip(S,codes):v[x]=(1,0,-1,0)[k-16];w[x]=(0,1,0,-1)[k-16]
        re=R@v-I@w;im=R@w+I@v;norm=re*re+im*im
        demand(np.all(norm.sum(axis=1)==Q*h),'bad group scaling')
        nz=np.count_nonzero(norm,axis=1)
        flat=(nz>=h)&(norm.max(axis=1)*nz==Q*h)
        # Exact constraint implication via support masks; eliminate one mandatory context at a time.
        remaining={*range(1,256)};fi=np.flatnonzero(flat);depth=0
        while True:
            occ=Counter(E[fi].ravel().tolist())
            if not remaining or not fi.size:break
            if any(not occ[x] for x in remaining):break
            mins=[x for x in remaining if occ[x]==1];demand(mins,'LP not excluded')
            x=min(mins);j=next(i for i in fi if x in E[i]);z=set(E[j])
            demand(z<=remaining,'overlapping forced rows');remaining-=z
            fi=np.array([i for i in fi if z.isdisjoint(E[i])],dtype=int);depth+=1
        demand(remaining and any(not occ[x] for x in remaining),'not contradicted')
        rows[row]+=1;depths[depth]+=1
    demand([rows[i] for i in range(8)]==[1,4,4,16,16,64,56,64],'bad case count')
    print("direct chirp amplitudes / cover contradictions:",dict(depths))
if __name__=="__main__":run(sys.argv[1])
