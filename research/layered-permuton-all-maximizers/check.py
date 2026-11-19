"""Exact finite replays illustrating local statements, not a proof over permutons.
Standard-library Python 3.10+, works with -O. No network or file inputs."""
from collections import Counter
from functools import lru_cache
from itertools import permutations,combinations,product
from math import comb,factorial

def req(v,msg):
    if not v: raise ArithmeticError(msg)

def pat(seq):
    ranks={v:j for j,v in enumerate(sorted(seq))}
    return tuple(ranks[v] for v in seq)

def islayer(s):
    if not s: return True
    pos=s.index(0)
    return s[:pos+1]==tuple(range(pos,-1,-1)) and islayer(tuple(x-pos-1 for x in s[pos+1:]))

def clone(p,i,j):
    # Remove j; replace i by a decreasing pair. Double all values first.
    vals=[]
    for k,v in enumerate(p):
        if k==j:continue
        if k==i:vals.extend((2*v+1,2*v))
        else:vals.append(2*v)
    return pat(vals)

def order(p,i,j):
    if i<j and p[i]<p[j]:return -1
    if i>j and p[i]>p[j]:return 1
    return 0

def comps(p):
    n=len(p);ds=list(range(n))
    def find(i):
        while ds[i]!=i:i=ds[i]
        return i
    for i,j in combinations(range(n),2):
        if p[i]>p[j]:ds[find(i)]=find(j)
    return {frozenset(j for j in range(n) if find(j)==find(i)) for i in range(n)}

def roots_and_intervals():
    paths=roots=lab=0
    for n in range(2,9):
        for p in permutations(range(n)):
            paths+=1
            a=0; bands=[]
            for b in range(1,n+1):
                if max(p[:b])+1==b:
                    bands.append(frozenset(range(a,b)));a=b
            req(set(bands)==comps(p),"finite inversion spans / direct sum cuts")
            if not islayer(p):continue
            for i,j in combinations(range(n),2):
                if p[i]<p[j]:continue
                req(clone(p,i,j)==p and clone(p,j,i)==p,"incomparable clones destroy target")
                roots+=1
                for z in range(n):
                    if z in (i,j):continue
                    req(order(p,i,z)==order(p,j,z),"relation-signature")
                    lab+=1
    print("Permutation diagrams n=2..8:",paths,"component decompositions.")
    print("All layered targets n=2..8:",roots,"inversion-root clone pairs;",lab,"label comparisons.")

@lru_cache(None)
def occup(m,s):
    if s==1:return ((m,),)
    return tuple((i,)+q for i in range(m+1) for q in occup(m-i,s-1))

def inflate(perm,sgn,counts):
    seq=[]
    for i,k in enumerate(counts):
        seq.extend((perm[i],j if sgn[i]>0 else -j) for j in range(k))
    return pat(seq)

@lru_cache(None)
def density_counts(perm,weights,sgn,m):
    # Integer numerator of all pattern probabilities under a weighted monotone
    # inflation; common denominator (sum weights)^m. No with/without-replacement
    # conversion: keys on a single monotone segment have their prescribed order.
    c=Counter()
    for occ in occup(m,len(perm)):
        mult=factorial(m)
        for k in occ:mult//=factorial(k)
        for w,k in zip(weights,occ):mult*=w**k
        c[inflate(perm,sgn,occ)]+=mult
    req(sum(c.values())==sum(weights)**m,"multinomial total")
    return c

def ordinal(segments):
    perm=[];weights=[];sgn=[]
    for pp,ww,ss in segments:
        off=len(perm);perm.extend(x+off for x in pp);weights.extend(ww);sgn.extend(ss)
    return tuple(perm),tuple(weights),tuple(sgn)

def replace():
    # Formula (3): two fixed outside permutons and varying independent middle
    # permuton. Compute the whole pattern internally by inflation, compare with
    # the independent product of the three separately sampled pattern counts.
    left=((1,0),(1,2),(1,-1));right=((1,0),(1,1),(-1,1))
    total=tests=strict=0
    for rr in permutations(range(3)):
        for signs in product((1,-1),repeat=3):
            mid=(rr,(1,2,1),signs);den=sum(mid[1])
            def always(q):return tuple(range(q)),tuple(reversed(range(q)))
            mids=density_counts(*mid,2);qnum=mids[(1,0)]
            for m in range(3,8):
                direct=density_counts(*ordinal((left,mid,right)),m)
                seen=Counter()
                for a,r,b in occup(m,3):
                    A=density_counts(*left,a);M=density_counts(*mid,r);B=density_counts(*right,b)
                    mult=comb(m,a)*comb(m-a,r)
                    for p,wa in A.items():
                        for u,wu in M.items():
                            for v,wv in B.items():
                                out=p+tuple(a+j for j in u)+tuple(a+r+j for j in v)
                                seen[out]+=wa*wu*wv*mult
                req(seen==direct,"conditional replacement polynomial")
                total+=1;tests+=len(set(seen)|set(direct))
                if 0<qnum<den**2:
                    c=density_counts(*mid,m);inc,dec=always(m)
                    req(c[inc]<(den**2-qnum)*den**(m-2) and c[dec]<qnum*den**(m-2),"strict monotone slack")
                    strict+=1
    print("Exact replacement distributions:",total,"for m=3..7;",tests,"positive pattern weights.")
    print("Mixed monotone strictness pairs (both colors):",strict)
if __name__=="__main__":
    roots_and_intervals()
    replace()
