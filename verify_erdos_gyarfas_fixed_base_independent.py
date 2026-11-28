#!/usr/bin/env python3
"""Independent exact HNF scan for the fixed K3,3 base (no input certificate)."""
from itertools import combinations, product
from functools import lru_cache
from math import gcd
from collections import defaultdict, Counter
import sys

ZERO = (0,0,0,0)
COTREE = ((1,4),(1,5),(2,4),(2,5))
ADJ = [range(3,6) if v<3 else range(3) for v in range(6)]
SHIFT = {(i,j): tuple((1 if i<j else -1)*int(tuple(sorted((i,j)))==c)
                       for c in COTREE)
          for i in range(6) for j in ADJ[i]}


def neg(x):
    return tuple(-a for a in x)


def add(x,y):
    return tuple(a+b for a,b in zip(x,y))


def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))


def norm(x):
    return max(x,neg(x))


def words(n):
    """Assemble the cycle from two nonbacktracking halves with the same endpoints."""
    for v in range(3):
        by_end = defaultdict(list)
        def extend(last, prev, path, prefix, left):
            if left==0:
                by_end[last].append((path,prefix))
                return
            for w in ADJ[last]:
                if w!=prev and (w>=3 or w>=v):
                    extend(w,last,path+(w,),prefix+(add(prefix[-1],SHIFT[last,w]),),left-1)
        extend(v,-1,(v,),(ZERO,),n//2)
        for paths in by_end.values():
            for (A,P),(B,Q) in combinations(paths,2):
                if A[1]==B[1] or A[-2]==B[-2]:
                    continue
                # The endpoint offset is the closing condition. Once it vanishes,
                # the two halves start at the same vertex and end at the same vertex.
                yield norm(sub(P[-1],Q[-1])),tuple(zip(A,P))+tuple(zip(B[1:-1],Q[1:-1]))


def witness_clauses():
    short = [set(t for t,_ in words(n)) for n in (4,8)]
    shorter=short[0]|short[1]
    more=defaultdict(set)
    @lru_cache(None)
    def coset_rules(t):
        if t==ZERO:
            return (lambda b:norm(b)), shorter
        i=next(i for i,x in enumerate(t) if x)
        if t[i]<=0: raise AssertionError('nonpositive coset pivot')
        def key(b):
            def rem(v):
                q=v[i]//t[i]
                return tuple(x-q*y for x,y in zip(v,t))
            return min(rem(b),rem(neg(b)))
        return key, {key(b) for b in shorter}
    for t,pts in words(16):
        if t in shorter or frozenset() in more[t]:
            continue
        key, excluded=coset_rules(t)
        D=set()
        for (u,a),(v,b) in combinations(pts,2):
            if u==v:
                k=key(sub(a,b))
                if k==ZERO: break
                if k not in excluded:
                    D.add(k)
        else:
            D=frozenset(D)
            if not any(F<=D for F in more[t]):
                more[t]={F for F in more[t] if not D<=F}
                more[t].add(D)
    return short,more


@lru_cache(None)
def residue_masks(a,c):
    g=gcd(a,c)
    m=a//g
    cinv=pow(c//g,-1,m) if m>1 else 0
    bits=tuple(sum(1<<w for w in range(i,a,m)) for i in range(m))
    return tuple(0 if r%g else bits[(cinv*(r//g))%m] for r in range(a))


def census(n,short,more, collect=False):
    count=leftover=0
    solutions=[]
    def sk(v):
        return sum(map(abs,v)),v
    early = sorted(short[0],key=sk)+sorted(short[1]-short[0],key=sk)
    later = sorted([t for t,ns in more.items() if frozenset() in ns],key=sk)
    pure = early+later
    conditional=[(t,tuple(S)) for t,ns in sorted(more.items()) for S in sorted(ns,key=lambda x:(len(x),sorted(x))) if S]
    for a in range(1,n+1):
        if n%a: continue
        allw=(1<<a)-1
        for b in range(1,n//a+1):
            if n%(a*b): continue
            for c in range(1,n//(a*b)+1):
                if n%(a*b*c): continue
                d=n//(a*b*c)
                for x,y,z in product(range(b),range(b),range(c)):
                    count+=a**3
                    def reduce(v):
                        t,r=divmod(v[3],d)
                        if r: return
                        s,r=divmod(v[2]-z*t,c)
                        if r: return
                        q,r=divmod(v[1]-x*s-y*t,b)
                        if r: return
                        return v[0],q,s,residue_masks(a,t%a)
                    simple=[R for v in pure if (R:=reduce(v)) is not None]
                    if any(t==u==v==0 and m[0]==allw for t,u,v,m in simple):
                        continue
                    composite=[(R,tuple(S for v in vs if (S:=reduce(v)) is not None))
                               for t,vs in conditional if (R:=reduce(t)) is not None]
                    for u in range(a):
                        # Reduce the u-coordinate once, before varying v,w.
                        S1=[(t-q*u,s,m) for t,q,s,m in simple]
                        C1=[((t-q*u,s,m),tuple((f-g*u,h,n) for f,g,h,n in F))
                            for (t,q,s,m),F in composite]
                        for v in range(a):
                            bad=0
                            for t,s,m in S1:
                                bad|=m[(t-s*v)%a]
                                if bad==allw: break
                            if bad!=allw:
                                for (t,s,m),F in C1:
                                    tmask=m[(t-s*v)%a] & ~bad
                                    if tmask:
                                        for f,h,mf in F:
                                            tmask&=~mf[(f-h*v)%a]
                                        bad|=tmask
                                        if bad==allw: break
                            for_pass=allw^bad
                            leftover+=for_pass.bit_count()
                            if collect:
                                while for_pass:
                                    bit=for_pass&-for_pass
                                    w=bit.bit_length()-1
                                    solutions.append((a,b,c,d,u,v,w,x,y,z))
                                    for_pass-=bit
    divisor_count=sum(a**3*b**2*c for a in range(1,n+1) if n%a==0
                      for b in range(1,n//a+1) if n%(a*b)==0
                      for c in range(1,n//(a*b)+1) if n%(a*b*c)==0)
    if divisor_count!=count:
        raise AssertionError(("HNF count",n,count,divisor_count))
    return count,leftover,solutions



def census_arrays(n,short,more):
    """Optional speed-up for the modular masks; all operations are exact."""
    import numpy as np
    count=leftover=0

    def sk(v): return sum(map(abs,v)),v
    early=sorted(short[0],key=sk)+sorted(short[1]-short[0],key=sk)
    later=sorted([t for t,ns in more.items() if frozenset() in ns],key=sk)
    pure=early+later
    conditional=[(t,tuple(S)) for t,ns in sorted(more.items())
                 for S in sorted(ns,key=lambda x:(len(x),sorted(x))) if S]
    for a in range(1,n+1):
        if n%a: continue
        allw=(1<<a)-1
        W=(a+63)//64
        mask64=(1<<64)-1
        def limbs(x):
            return [(x>>(64*i))&mask64 for i in range(W)]
        tables=np.asarray([[limbs(w) for w in residue_masks(a,t)] for t in range(a)],
                          dtype=np.uint64)
        full=np.asarray(limbs(allw),dtype=np.uint64)
        U=np.repeat(np.arange(a,dtype=np.int32),a)
        V=np.tile(np.arange(a,dtype=np.int32),a)
        for b in range(1,n//a+1):
            if n%(a*b): continue
            for c in range(1,n//(a*b)+1):
                if n%(a*b*c): continue
                d=n//(a*b*c)
                for x,y,z in product(range(b),range(b),range(c)):
                    count+=a**3
                    def reduce(v):
                        t,r=divmod(v[3],d)
                        if r: return
                        s,r=divmod(v[2]-z*t,c)
                        if r: return
                        q,r=divmod(v[1]-x*s-y*t,b)
                        if r: return
                        return v[0],q,s,t%a
                    simple=[R for v in pure if (R:=reduce(v)) is not None]
                    if any(t%a==u%a==v%a==k==0 for t,u,v,k in simple):
                        continue
                    composite=[(R,tuple(S for v in vs if (S:=reduce(v)) is not None))
                               for t,vs in conditional if (R:=reduce(t)) is not None]
                    if a<=16:
                        for u,v in product(range(a),repeat=2):
                            used=0
                            for t,q,s,k in simple:
                                used|=residue_masks(a,k)[(t-q*u-s*v)%a]
                                if used==allw: break
                            if used!=allw:
                                for (t,q,s,k),F in composite:
                                    yes=residue_masks(a,k)[(t-q*u-s*v)%a]&~used
                                    if yes:
                                        for f,g,h,j in F:
                                            yes&=~residue_masks(a,j)[(f-g*u-h*v)%a]
                                        used|=yes
                                        if used==allw: break
                            leftover+=(allw^used).bit_count()
                        continue
                    U1,V1=U,V
                    used=np.zeros((a*a,W),dtype=np.uint64)
                    for t,q,s,k in simple:
                        used|=tables[k,(t-q*U1-s*V1)%a]
                        live=np.any(used!=full,axis=1)
                        if not live.all():
                            U1,V1,used=U1[live],V1[live],used[live]
                            if not U1.size: break
                    if U1.size:
                        for (t,q,s,k),F in composite:
                            yes=tables[k,(t-q*U1-s*V1)%a]
                            for f,g,h,j in F:
                                yes&=~tables[j,(f-g*U1-h*V1)%a]
                            used|=yes
                            live=np.any(used!=full,axis=1)
                            if not live.all():
                                U1,V1,used=U1[live],V1[live],used[live]
                                if not U1.size: break
                    if U1.size:
                        leftover+=sum(int(t).bit_count() for t in (used^full).ravel())
    divisor_count=sum(a**3*b**2*c for a in range(1,n+1) if n%a==0
                      for b in range(1,n//a+1) if n%(a*b)==0
                      for c in range(1,n//(a*b)+1) if n%(a*b*c)==0)
    if divisor_count!=count: raise AssertionError(("array HNF count",n,count,divisor_count))
    return count,leftover

def projective(p):
    """All normalized lines in the dual of F_p^4."""
    return [((0,)*i+(1,)+a) for i in range(4)
            for a in product(range(p),repeat=3-i)]


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def scan133_crt(short,more):
    v7,v19=projective(7),projective(19)
    need7=short[0]|short[1]|set(more)
    all_forms=need7|{v for F in more.values() for s in F for v in s}
    if len(v7)*len(v19)!=2_896_000:
        raise AssertionError("wrong CRT chart size")
    all19=(1<<len(v19))-1
    mask={}
    for t in all_forms:
        b=bytearray((len(v19)+7)//8)
        t0,t1,t2,t3=t
        for i,(x,y,z,w) in enumerate(v19):
            if (t0*x+t1*y+t2*z+t3*w)%19==0:
                b[i//8]|=1<<(i%8)
        mask[t]=int.from_bytes(b,"little")
    pure=short[0]|short[1]
    cases=[]
    for a in v7:
        zero={t for t in all_forms if dot(a,t)%7==0}
        used=0
        for t in zero&pure:
            used|=mask[t]
        for t in (zero&need7)-pure:
            for S in more[t]:
                cover=mask[t]
                for s in S&zero:
                    cover&=~mask[s]
                used|=cover
        b=all19^used
        while b:
            z=b&-b
            cases.append((a,v19[z.bit_length()-1]))
            b-=z
    if len(cases)!=56:
        raise AssertionError(("CRT census",len(cases)))
    return cases


def volt_class(values,g,p):
    voltage={e:a for e,a in zip(COTREE,values)}
    def val(v,w):
        return voltage.get((v,w),0)-voltage.get((w,v),0)
    v=[]
    for i,j in COTREE:
        cycle=(i,j,0,3,i)
        v.append(sum(val(g[u],g[w]) for u,w in zip(cycle,cycle[1:]))%p)
    a=pow(next(x for x in v if x),-1,p)
    return tuple(x*a%p for x in v)


def check_orbits(cases):
    from itertools import permutations
    autos=[tuple(x+s for x in p)+tuple(x+3-s for x in q)
           for p in permutations(range(3)) for q in permutations(range(3)) for s in (0,3)]
    remaining=set(cases)
    canonical=[(77,84,8,26),(1,122,107,20),(1,122,103,64)]
    sizes=[]
    for v in canonical:
        images={(volt_class(v,g,7),volt_class(v,g,19)) for g in autos}
        if not images<=remaining: raise AssertionError(("orbit mismatch",v))
        remaining-=images
        sizes.append(len(images))
    if sizes!=[24,24,8] or remaining:
        raise AssertionError(("orbit sizes",sizes,len(remaining)))
    print("133-sheet CRT classes:",sizes,flush=True)
    expected=[(48368435850,1242076788981126),(48368435850,1242076788622026),
              (48368340090,1241736424975746)]
    for v,ref in zip(canonical,expected):
        volts=dict(zip(COTREE,v))
        graph=[tuple(w*133+(i+volts.get((u,w),0)-volts.get((w,u),0))%133
                     for w in ADJ[u]) for u in range(6) for i in range(133)]
        if any(has_cycle(graph,133,k) for k in (4,8,16)) or not has_cycle(graph,133,32):
            raise AssertionError(("literal cycle check",v))
        tr=traces(graph,133,20,30)
        if tr!=ref: raise AssertionError(("trace pair",v,tr))
        print("133-sheet representative:",v,tr,flush=True)


def make_graph(adj,chords,box,switch):
    r=len(box)
    coords=list(product(*map(range,box)))
    index={a:i for i,a in enumerate(coords)}
    N=len(coords)
    k={e:i for i,e in enumerate(chords)}
    out=[]
    for v,neighbors in enumerate(adj):
        increments=[]
        for w in neighbors:
            j=k.get((v,w),k.get((w,v),-1))
            increments.append((w,tuple((1 if v<w else -1)*int(i==j) for i in range(r))))
        for c in coords:
            out.append(tuple(w*N+index[switch(add(c,D))] for w,D in increments))
    return out


def has_cycle(graph,n,length):
    """Literal lift graph; pair half-path interiors as integer bitsets."""
    half=length//2
    for root in range(0,len(graph),n):
        last=defaultdict(list)
        def rec(v,rest,used):
            if not rest:
                inner=used^((1<<root)|(1<<v))
                old=last[v]
                if any(mask&inner==0 for mask in old):
                    return True
                old.append(inner)
                return False
            for w in graph[v]:
                if w>=root and not (used>>w)&1 and rec(w,rest-1,used|1<<w):
                    return True
            return False
        if rec(root,half,1<<root):
            return True
    return False


def traces(graph,n,*check):
    Q={k:0 for k in check}
    for root in range(0,len(graph),n):
        a=[0]*len(graph); a[root]=1
        for s in range(1,max(check)+1):
            a=[sum(a[w] for w in row) for row in graph]
            if s in Q: Q[s]+=a[root]*n
    return tuple(Q[k] for k in check)


def subdivided_k4():
    adj=((2,3,4),(2,3,4),(0,1,3),(0,1,2),(0,1))
    chords=((1,2),(1,3),(2,3))
    totals=[]; wins=[]
    for N in range(1,20):
        count=0
        for a in range(1,N+1):
            if N%a: continue
            for b in range(1,N//a+1):
                if N%(a*b): continue
                c=N//(a*b)
                for u,v,w in product(range(a),range(a),range(b)):
                    count+=1
                    def switch(R):
                        x,y,z=R
                        q,z=divmod(z,c); y-=q*w; x-=q*v
                        q,y=divmod(y,b); x-=q*u
                        return x%a,y,z
                    graph=make_graph(adj,chords,(a,b,c),switch)
                    if any(has_cycle(graph,N,i) for i in [4,8,16]):
                        continue
                    if (N,a,b,c)!=(19,19,1,1) or not has_cycle(graph,N,32):
                        raise AssertionError(("unexpected subdivided survivor",N,a,b,c))
                    wins.append((1,-u%19,-v%19))
        totals.append(count)
    if (sum(totals[:-1]),totals[-1])!=(4178,381) or sorted(wins)!=[(1,8,0),(1,8,7),(1,12,0),(1,12,11)]:
        raise AssertionError(("subdivided census",totals,wins))
    # The group of order four is generated by swaps (0 1), (2 3).
    # Check the four images by computing cotree voltage plus the return tree path.
    from itertools import product as tensor
    known=set(wins)
    graph_labels=dict(zip(chords,(1,8,0)))
    def label(i,j):
        return graph_labels.get((i,j),0)-graph_labels.get((j,i),0)
    cycles=((1,2,0,4,1),(1,3,0,4,1),(2,3,0,2))
    out=set()
    for a,b in tensor((0,1),repeat=2):
        perm=(1,0) if a else (0,1)
        perm+=((3,2) if b else (2,3))+(4,)
        w=[sum(label(perm[i],perm[j]) for i,j in zip(path,path[1:]))%19 for path in cycles]
        out.add(tuple(x*pow(w[0],-1,19)%19 for x in w))
    if out!=known:
        raise AssertionError(("subdivided orbit",known,out))
    print("subdivided K4: 4559 covers, one 19-sheet orbit of size 4",sorted(wins))

def main():
    args=sys.argv[1:]
    use_arrays="--arrays" in args
    if use_arrays: args.remove("--arrays")
    short,more=witness_clauses()
    histogram=sorted(Counter(len(x) for S in more.values() for x in S).items())
    if len(short[0])!=9 or len(short[1])!=45 or histogram!=[(0,501),(1,84)]:
        raise AssertionError(("unexpected independent clause histogram",histogram))
    if not args:
        check_orbits(scan133_crt(short,more))
        subdivided_k4()
    else:
        lo,hi=map(int,args)
        if not 1<=lo<=hi<=133:
            raise ValueError("Use an inclusive index range in 1..133")
        total=0
        for n in range(lo,hi+1):
            result=census_arrays(n,short,more) if use_arrays else census(n,short,more)
            count,left=result[:2]
            total+=count
            print(n,count,left,flush=True)
            if left!=(56 if n==133 else 0):
                raise AssertionError(("unexpected number of survivors",n,left))
        if (lo,hi)==(1,133) and total!=169240289:
            raise AssertionError(("unexpected total",total))
        print("PASS",lo,hi,total,flush=True)


if __name__=="__main__":
    main()
