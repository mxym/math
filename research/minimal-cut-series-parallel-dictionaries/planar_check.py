"""Finite consistency test of the prior-derived plane representation; standard library. No graph atlas used."""
from itertools import combinations,permutations,product

def go(n, masks=None):
    pairs=list(combinations(range(n),2));num=hits=counts=0
    def cc(A,rm):
        todo=set(range(n))-rm;out=[]
        while todo:
            a=todo.pop();seen={a};q=[a]
            while q:
                a=q.pop()
                for u in A[a]:
                    if u in todo: todo.remove(u);seen.add(u);q.append(u)
            out.append(seen)
        return out
    def rotfaces(R):
        darts={(u,v) for u in range(n) for v in R[u]};fs=[]
        while darts:
            s,t=next(iter(darts));x,y=s,t;f=[]
            while True:
                darts.remove((x,y));f.append(x);l=R[y];x,y=y,l[(l.index(x)+1)%len(l)]
                if (x,y)==(s,t):break
            fs.append(f)
        return fs
    for m in (range(1<<len(pairs)) if masks is None else masks):
        A=[[] for _ in range(n)]
        for i,(u,v) in enumerate(pairs):
            if m>>i&1:A[u].append(v);A[v].append(u)
        if min(map(len,A))<2 or any(len(cc(A,{v}))!=1 for v in range(n)):continue
        cut=[]
        for T in range(1,1<<n):
            S={x for x in range(n) if T>>x&1}
            if len(S)>=3:
                comps=cc(A,S)
                if len(comps)>1 and all(all(set(A[x])&C for C in comps) for x in S):cut.append(S)
        if not cut:continue
        rots=[[(r[0],)+p for p in permutations(r[1:])] for r in A]
        for R in product(*rots):
            fs=rotfaces(R)
            if n-m.bit_count()+len(fs)!=2:continue
            num+=1
            for S in cut:
                E={e for f in fs for e in combinations(sorted(S&set(f)),2)}
                if len(E)!=len(S) or any(sum(x in e for e in E)!=2 for x in S):
                    raise RuntimeError((R,S,fs,E))
                a=min(S);reach={a}
                for _ in S:
                    for v,w in E:
                        if v in reach or w in reach:reach.update([v,w])
                if reach!=S: raise RuntimeError('not connected')
                hits+=1
            counts+=1
    return num,hits
# Biconnected planar graphs must have at least 5 vertices to have 3-point global cuts.
print('5 vertices, plane rotations with nontrivial cut and inspected cut sets:',go(5))

# Every chord insertion into the same cyclic order on a K_{2,4} scaffold,
# except the two poles joined (which eliminates the candidate central cut).
# Include all 16 choices of additional ring edges and every spherical rotation.
E=list(combinations(range(6),2));fixed={tuple(sorted((i,j))) for i in (0,1) for j in range(2,6)}
ring=[(2,3),(3,4),(4,5),(2,5)]
masks=[sum(1<<E.index(e) for e in fixed|{f for j,f in enumerate(ring) if bits>>j&1}) for bits in range(16)]
print('K_{2,4} with subsets of the four ring edges, rotations/cuts:',go(6,masks))
