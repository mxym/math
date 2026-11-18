"""Independent exact finite diagnostics: partition Möbius, matrix-tree, Euler zigzags.
No numerical roots or floating-point comparisons. No imports from author verifier.
"""
from itertools import combinations
from math import comb, factorial, prod
from collections import Counter
from functools import lru_cache

def require(ok, label):
    if not ok: raise ValueError(label)

def patterns(n):
    """Restricted-growth words for set partitions; labels are vertex numbers."""
    def rec(w,groups):
        if len(w)==n:
            yield w,groups
            return
        for t in range(groups+1):
            yield from rec(w+(t,),max(t+1,groups))
    yield from rec((0,),1)

def det(mat):
    if not mat: return 1
    return sum((-1)**j*x*det([r[:j]+r[j+1:] for r in mat[1:]]) for j,x in enumerate(mat[0]) if x)

def census():
    count=0
    for n in range(2,6):
        edges=list(combinations(range(n),2));r=n-1
        terms=[(sum(1<<i for i,(a,b) in enumerate(edges) if w[a]!=w[b]),
                 (-1)**(k-1)*factorial(k-1)) for w,k in patterns(n)]
        for mask in range(1<<len(edges)):
            L=[[0]*n for i in range(n)]
            for j,(a,b) in enumerate(edges):
                if mask>>j&1:L[a][a]+=1;L[b][b]+=1;L[a][b]-=1;L[b][a]-=1
            tau=det([l[:-1] for l in L[:-1]])
            if not tau: continue
            count+=1;m=mask.bit_count()
            C=[0]*(m+1)
            for crosses,mu in terms: C[(crosses&mask).bit_count()]+=mu
            require(C[0]==1 and C[m]!=0,(n,mask,'ends'))
            require(sum(map(abs,C))<=2**r*tau<=2**r*comb(m,r),(n,mask,'norms'))
            # Divide by (1-q) repeatedly by prefix summation, rejecting nonzero remainder.
            H=C[:]
            for _ in range(r):
                H=[sum(H[:j+1]) for j in range(len(H))]
                require(H.pop()==0,('factor',n,mask))
            require(all(h>=0 for h in H) and sum(H)==tau and H[-1]>0,(n,mask,'H'))
    require(count==771,'connected graph count')
    return count

def shapes(n,mn=1):
    if not n:
        yield ()
        return
    for a in range(mn,n+1):
        for tail in shapes(n-a,a): yield (a,)+tail

@lru_cache(None)
def shape_terms(n):
    # Collapse the partition-lattice formula by block shape; coefficients integer.
    acc=Counter(); h=n*(n-1)//2; nf=factorial(n)
    for shape in shapes(n):
        freq=Counter(shape); k=len(shape)
        den=prod(factorial(s)**a*factorial(a) for s,a in freq.items())
        c=h-sum(a*(s*(s-1)//2) for s,a in freq.items())
        acc[c]+=((-1)**(k-1)*factorial(k-1))*(nf//den)
    return tuple((e,coef) for e,coef in acc.items() if coef)

def rational_sign(n,a,b):
    d=n*(n-1)//2
    v=sum(coef*pow(a,e)*pow(b,d-e) for e,coef in shape_terms(n))
    return (v>0)-(v<0)

def test_kn():
    # Classical Entringer triangle: E_j = # alternating permutations on j points.
    row=[1];zig=[1]
    for j in range(1,33):
        prev=row[::-1];row=[0]
        for x in prev:row.append(row[-1]+x)
        zig.append(row[-1])
    for n in range(1,34):
        end=sum(c*(-1)**e for e,c in shape_terms(n))
        ref=(-1)**(n*(n-1)//2+n-1)*2**(n-1)*zig[n-1]
        require(end==ref,('Euler',n))
    signs=[(7,-659,-658),(8,-696,-695),(15,-760,-759),(16,-771,-770),(31,-839,-838),(32,-842,-841),(63,-898,-897),(64,-899,-898)]
    for n,a,b in signs:
        require(rational_sign(n,a,1000)==-1 and rational_sign(n,b,1000)==1,('bracket',n))
    return len(signs)

if __name__=='__main__':
    n=census();b=test_kn()
    print('PASS:',n,'connected labelled graphs, 33 endpoint identities,',b,'root brackets through n=64.')
