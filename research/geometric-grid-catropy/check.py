"""Finite exact tests of trace/entropy proof ingredients. Python 3.10+, stdlib."""
from itertools import product,combinations
from collections import defaultdict,Counter
from math import comb
from fractions import Fraction

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)

def proj(word,edges,s):
    return tuple(bytes(x for x in word if x==i or x==j) for i,j in [(a,a) for a in range(s)]+edges)

def minmax(word,edges):
    n=len(word);e=set(edges)
    prev=[set() for _ in word]
    for j,y in enumerate(word):
        for i,x in enumerate(word[:j]):
            if x==y or tuple(sorted((x,y))) in e:prev[j].update(prev[i]|{i})
    return tuple((len(a),n-1-sum(i in s for s in prev)) for i,a in enumerate(prev))

def slots(word,edges,starts):
    mm=minmax(word,edges);out=[]
    for l in starts:
        if mm[l]!=(l,l) or mm[l+4]!=(l+4,l+4) or word[l]!=1 or word[l+4]!=1:continue
        ins=word[l+1:l+4]
        if ins==(0,1,2):out.append((l,0))
        if ins in ((0,2,1),(2,0,1)):out.append((l,1))
    return out

def cube_test(s,n,starts,edges):
    # Full length-n word enumeration; trace inferred from *all* projections
    # to dependent pairs. Compute true word multiplicity, not its formula.
    counts=Counter();rep={}
    for w in product(range(s),repeat=n):
        h=proj(w,edges,s);counts[h]+=1;rep[h]=w
    edges_checked=eligible_traces=double=0
    for h,w in rep.items():
        ss=slots(w,edges,starts)
        if ss:eligible_traces+=1
        if len(ss)>1:double+=1
        for l,t in ss:
            other=w[:l+1]+((0,1,2) if t else (0,2,1))+w[l+4:]
            g=proj(other,edges,s)
            exp=[(pos,1-bit if pos==l else bit) for pos,bit in ss]
            need(slots(rep[g],edges,starts)==exp,"eligibility changed under switch")
            need((counts[g]*2==counts[h]) if t else (counts[g]==counts[h]*2),"not exact 1:2 word count")
            edges_checked+=1
    need(edges_checked and (len(starts)==1 or double),"vacuous switch test")
    return len(counts),eligible_traces,edges_checked,double

def refine(matrix):
    out=[]
    for r,row in enumerate(matrix):
        for c,x in enumerate(row):
            if x:
                out+= [(2*r+(u if x==1 else 1-u),2*c+u) for u in (0,1)]
    return out
def grid_test(matrix,n):
    cells=refine(matrix);s=len(cells)
    edges=[(i,j) for i,j in combinations(range(s),2) if cells[i][0]==cells[j][0] or cells[i][1]==cells[j][1]]
    seen={};rev={}
    for w in product(range(s),repeat=n):
        # offset (j+1)/(n+1), oriented by refined strip parity
        xy=[(c*(n+1)+(n-j if c%2 else j+1),r*(n+1)+(n-j if r%2 else j+1),r,c)
            for j,i in enumerate(w) for r,c in [cells[i]]]
        rows=tuple(sorted(z[2] for z in xy));cols=tuple(sorted(z[3] for z in xy))
        # An offset can equal the endpoint of the *next* strip only at j=n,
        # which does not occur. All sampled coordinates are distinct.
        ys=sorted(z[1] for z in xy);p=tuple(ys.index(z[1]) for z in sorted(xy))
        gr=(p,rows,cols);t=proj(w,edges,s)
        need(gr not in seen or seen[gr]==t,"gridded sample fails to determine trace")
        need(t not in rev or rev[t]==gr,"trace fails to determine gridding")
        seen[gr]=t;rev[t]=gr
    return s**n,len(seen)
def chunk_test():
    out={};edges=[(0,1),(1,2)]
    for w in product(range(3),repeat=8):
        k=4
        key=proj(w,edges,3),tuple(w[:k].count(i) for i in range(3))
        chunks=proj(w[:k],edges,3),proj(w[k:],edges,3)
        need(key not in out or out[key]==chunks,"chunk reconstruction")
        out[key]=chunks
    return len(out)
def masks():
    cnt=0
    for n in range(1,12):
        for k in range(n+1):
            N=n-k
            for a in range(N+1):
                # Y= B^a A B^(N-a-1) if a<N, otherwise all B; insertions
                # per gap checked under uniform fixed-K masks including ends.
                gap_slots=(a+1,N-a) if a<N else (N+1,)
                sums=[0]*len(gap_slots)
                for mask in combinations(range(n),k):
                    mask=set(mask);old=0
                    for i in range(n):
                        if i in mask:sums[int(a<N and old>a)]+=1
                        else:old+=1
                for s,g in zip(sums,gap_slots):need(Fraction(s,comb(n,k))==Fraction(k*g,N+1),"wrong mean insertions")
                cnt+=1
    return cnt

if __name__=="__main__":
    print("Cube on P3, n=10, two disjoint slots (traces, eligible, flips, double):",cube_test(3,10,[0,5],[(0,1),(1,2)]))
    print("Cube on P4, n=8, one slot (traces, eligible, flips, double):",cube_test(4,8,[2],[(0,1),(1,2),(2,3)]))
    print("Signed 2x2 refinements, n=4 (words, gridded traces):",
          [grid_test(m,4) for m in (((1,1),(1,1)),((1,1),(1,-1)),((1,1),(0,1)))])
    print("Distinct trace/count pairs recovering both chunks:",chunk_test())
    print("Exact uniform-mask gap cases:",masks())
