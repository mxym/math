"""Exact independent check using whole finite-tree distributions and interpolation.
No graph or series packages, no imports from the proof author's checkers."""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial
from collections import Counter
from functools import lru_cache

def check(v,msg):
    if not v: raise ArithmeticError(msg)

def trees(n):
    """Literal edge subsets, without a Prüfer or tree-support enumerator."""
    for edges in combinations(combinations(range(n),2),n-1):
        seen={0}
        for _ in range(n-1):
            for u,v in edges:
                if u in seen or v in seen: seen.update((u,v))
        if len(seen)==n: yield edges

def fs(n,h):
    return F(factorial(n),factorial(n-h)*n**(h-1)) if h<=n else F(0)

@lru_cache(None)
def log_jets(z,d=6):
    """Expand log(1+w) directly, not via derivative identity or Poisson iteration."""
    acc=[F(0)]*(d+1); power=[1]+[0]*d;w=list(z)+[0]*(d+1-len(z));w[0]=0
    for i in range(1,d+1):
        power=[sum(power[j]*w[h-j] for j in range(h+1)) for h in range(d+1)]
        for j in range(i,d+1):acc[j]+=F((-1)**(i-1)*power[j],i)
    return tuple(acc)

def main():
    D=6; means={};leaf_tests=0;total=0
    for n in range(1,8):
        set_counts=[0]*(n+1);plant_leaf=[0]*(n+1);freq=Counter();leafs=0;ntrees=0
        for ed in trees(n):
            e=[(1<<u)|(1<<v) for u,v in ed]
            leaves=sum(sum(i in pair for pair in ed)==1 for i in range(n))
            ns=[0]*(n+1)
            for mask in range(1<<n):
                if all(mask&pair!=pair for pair in e):
                    ns[mask.bit_count()]+=1
            freq[tuple(ns)]+=1;leafs+=leaves;ntrees+=1
            for k,c in enumerate(ns):
                set_counts[k]+=c;plant_leaf[k]+=c*leaves
        check(ntrees==(n**(n-2) if n>1 else 1),('Cayley',n))
        if n>=2:
            check(F(leafs,ntrees)==n*F(n-1,n)**(n-2),('base',n))
            for k in range(1,n):
                m=n-k
                pred=F(n-1,n)**(m-1)*(k+m*F(m-1,m)**(k-1))
                check(F(plant_leaf[k],set_counts[k])==pred,('planted leaf',n,k))
                check(F(set_counts[k],ntrees)==comb(n,k)*F(m,n)**(k-1),('annealed',n,k))
                leaf_tests+=1
        means[n]=[sum(q*log_jets(z)[j] for z,q in freq.items())/ntrees for j in range(D+1)]
        total+=ntrees
    qrow=[]
    for j in range(1,D+1):
        # finite means at n=1..j solve E c_j = sum_{h<=j} B_h (n)_h/n^{h-1}.
        # This follows from additive connected support and Cayley's forest count.
        b={}
        for n in range(1,j+1):
            b[n]=(means[n][j]-sum(v*fs(n,h) for h,v in b.items()))/fs(n,n)
        for n in range(j+1,8):
            check(means[n][j]==sum(v*fs(n,h) for h,v in b.items()),('fresh order',j,n))
        qrow.append(sum(b.values()))
    # Independent annealed calculation: If p_A'(b(z)) in log parameter is
    # a=b/(1+b), z=b(1+b)exp(b), then the Lagrange coefficient j^2[p_A]_j
    # equals [u^(j-1)] (1+u)^(-j-2) exp(-ju). Evaluate using derivatives.
    ann=[]
    for j in range(1,D+1):
        target=j-1;den=factorial(target)*j*j
        rising=1;num=0
        for i in range(target+1):
            num+=comb(target,i)*(-1)**i*rising*(-j)**(target-i)
            rising*=j+2+i
        ann.append(F(num,den))
    check(qrow==[F(1),F(-3,2),F(23,6),F(-149,12),F(1843,40),F(-3741,20)],('finite moments',qrow))
    check([a-q for a,q in zip(ann,qrow)]==[0]*5+[F(1,4)],('annealed',ann))
    print('Whole labeled trees, orders 1..7:',total,'; exact joint size/leaf tests, planted layers:',leaf_tests)
    print('Whole-tree triangular interpolation (order 7 independently held out in every column)')
    print('quenched   ',*[str(x) for x in qrow]);print('annealed   ',*[str(x) for x in ann])
    print('PASS')
if __name__=='__main__':main()
