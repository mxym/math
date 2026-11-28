#!/usr/bin/env python3
"""Independent exact packet oracle for the coherent ten and single-defect nine cases."""
import sys, itertools as it
from collections import defaultdict,Counter
from math import factorial
def rankings(n,allow):
    out=defaultdict(list)
    def rec(p,inversions,exception):
        if len(p)==n:out[exception].append(bytes(p));return
        for x in range(n):
            if x in p:continue
            # A new decreasing triple ends at x; its earlier two entries
            # must be one of the decreasing pairs already present in the prefix.
            new=[(x,b,c)for c,b in inversions if x<b]
            if len(new)+int(exception is not None)>allow:continue
            rec(p+[x],inversions+[(b,x)for b in p if b>x],new[0]if new else exception)
    rec([],[],None)
    return out
def prepare(P,n,exc):
    rows=[]
    for a,c in it.combinations(range(n),2):
        B=[b for b in range(a+1,c)if (a,b,c)!=exc]
        if not B:continue
        cell=defaultdict(int)
        for k,p in enumerate(P):
            pa,pc=p.index(a),p.index(c)
            if pa<pc:continue
            sig=tuple(int(p.index(b)<pc)for b in B)
            assert all(p.index(b)<pc or p.index(b)>pa for b in B)
            cell[sig]|=1<<k
        if len(cell)>1:
            blocks=tuple(sorted(cell.values(),key=int.bit_count,reverse=True))
            rows.append((sum(blocks),blocks))
    return sorted(rows,key=lambda ab:-(ab[0].bit_count()-ab[1][0].bit_count()))
def enumerate_domains(P,n,exc,cut):
    rows=prepare(P,n,exc); found=set();steps=0
    def walk(S):
        nonlocal steps
        steps+=1; size=S.bit_count()
        if size<cut:return
        R=[]
        for u,group in rows:
            T=S&u;cnt=T.bit_count()
            if cnt<2:continue
            counts=[(h.bit_count(),h)for g in group if (h:=S&g)]
            if len(counts)<=1:continue
            loss=cnt-max(x for x,b in counts)
            if size-loss<cut:return
            rem=size-cnt
            live=[b for x,b in counts if x+rem>=cut]
            R.append((loss,T,counts,live))
        if not R:found.add(S);return
        # Exact independently computed greedy disjoint subtraction: use large
        # losses first. A surviving domain intersects each disjoint piece in one block.
        rem=S; ub=size
        for loss,T,counts,live in sorted(R,key=lambda r:-r[0]):
            part=T&rem
            if not part:continue
            ub-=part.bit_count()-max((part&h).bit_count()for _,h in counts)
            if ub<cut:return
            rem &=~part
        loss,T,counts,live=min(R,key=lambda r:(len(r[3]),-r[0],r[1].bit_count()))
        outside=S&~T
        for block in live:walk(outside|block)
    walk((1<<len(P))-1)
    return [{P[i]for i in range(len(P))if g>>i&1}for g in found],steps
def canonical(D,n):
    # Unlike testing every order-to-identity map, use a vertex invariant of
    # the labelled pair-frequency matrix. Enumerate every unresolved row tie.
    B=[[sum(p.index(i)<p.index(j) for p in D)for j in range(n)]for i in range(n)]
    C=defaultdict(list)
    for i,row in enumerate(B):C[tuple(sorted(row))].append(i)
    blocks=[C[k]for k in sorted(C)];best=None;aut=0
    for comb in it.product(*(it.permutations(b)for b in blocks)):
        order=sum(comb,());inv=bytes(order.index(i)for i in range(n))
        tr=bytes.maketrans(bytes(range(n)),inv)
        key=b''.join(sorted(p.translate(tr) for p in D))
        if best is None or key<best:best,aut=key,1
        elif key==best:aut+=1
    return best,aut
def regular(n):
    P=rankings(n,0)[None];cut={9:465,10:1046}[n]
    D,s=enumerate_domains(P,n,None,cut)
    print('bound',n,len(P),s,Counter(map(len,D)),flush=True)
    assert len(D)==(40 if n==10 else 16) and set(map(len,D))=={cut}
    C=Counter();dual={}
    for d in D:
        assert all(len({bytes(i for i in p if i in t) for p in d})==4 for t in it.combinations(range(n),3))
        k,a=canonical(d,n);assert a==1
        kr,_=canonical({p[::-1]for p in d},n);C[k]+=1;dual[k]=kr
    assert all(dual.get(dual[k])==k for k in C)
    print('class sizes',sorted(C.values()),'self-dual classes',sum(k==v for k,v in dual.items()),flush=True)
    assert (sorted(C.values()),sum(k==v for k,v in dual.items()))==(([4]*2+[8]*4,4)if n==10 else ([4]*4,0))
def exceptional(start,end):
    n=9;Q=rankings(n,1);assert len(Q[None])==4862 and sum(len(v)for k,v in Q.items()if k is not None)==6188
    allT=list(it.combinations(range(n),3));nodes=0
    for k in range(start,end):
        T=allT[k];a,b,c=T
        P=[p for p in Q[None] if p.index(b)>min(p.index(a),p.index(c))]+Q[T]
        assert all(p.index(b)>min(p.index(a),p.index(c))for p in P)
        D,s=enumerate_domains(P,n,T,477);nodes+=s
        assert not D
        if (k+1)%10==0:print('checked',k+1,'total nodes',nodes,flush=True)
    print('PASS defect',start,end,'nodes',nodes,flush=True)
def literal(n,styles,T):
    pairs=[(a,c)for a,c in it.combinations(range(n),2)if c>a+1];mask=dict(zip(pairs,styles))
    # For each potential next-ranked letter, list all possible earlier sets
    # of size <= n. An invalid 1N3 occurs on appending a after both b,c;
    # an invalid 3N1 may be determined immediately on appending c before both.
    good={}
    for rem in range(1<<n):
        for x in range(n):
            if rem>>x&1:continue
            ok=True
            for a,b,c in it.combinations(range(n),3):
                if T==(a,b,c):bad=(x==b and not rem>>a&1 and not rem>>c&1)
                elif mask[a,c]>>(b-a-1)&1:bad=(x==c and not rem>>a&1 and not rem>>b&1)
                else:bad=(x==a and rem>>b&1 and rem>>c&1)
                if bad:ok=False;break
            good[rem,x]=ok
    D=[]
    def rec(p,seen):
        if len(p)==n:D.append(bytes(p));return
        for i in range(n):
            if not seen>>i&1 and good[seen,i]:rec(p+[i],seen|1<<i)
    rec([],0);count=len(D);return count,(0 if T is None else sum(p.index(T[2])<p.index(T[1])<p.index(T[0])for p in D))
def lower():
    ten=[0,0,4,2,12,18,82,210,0,2,1,6,9,41,105,1,1,3,3,11,43,0,1,2,10,26,1,1,5,13,0,1,5,1,3,1]
    nine=[0,1,2,10,5,26,37,1,1,5,5,13,21,0,1,1,5,9,1,1,3,5,0,1,2,1,1,1]
    assert literal(10,ten,None)==(1046,0);assert literal(9,nine,(5,7,8))==(476,76)
    for n,cut in enumerate((1,2,4,9,19,43,94,211),1):
        Ds,s=enumerate_domains(rankings(n,0)[None],n,None,cut);assert Ds and all(len(D)==cut for D in Ds)
    print("PASS both literal witnesses and all n<=8 bounds")
if __name__=='__main__':
    if sys.argv[1]=='lower':lower()
    elif sys.argv[1]=='defect':exceptional(*map(int,sys.argv[2:4]))
    else:regular(int(sys.argv[1]))
