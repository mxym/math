"""Fixed finite checks of the cyclotomic value and degree inequalities."""
from fractions import Fraction as Q
from math import gcd, isqrt, prod

def divisors(m):
    return [d for d in range(1,m+1) if m%d==0]

def mu(m):
    ret=1
    j=2
    while j*j<=m:
        if m%j==0:
            m//=j
            ret=-ret
            if m%j==0: return 0
        j+=1
    return -ret if m>1 else ret

values={}
tests=0
for x in range(2,13):
    val={}
    for m in range(1,76):
        D=divisors(m)
        top=x**m-1
        den=prod(val[d] for d in D if d!=m)
        v,rem=divmod(top,den)
        assert rem==0
        val[m]=v
        phi=sum(gcd(j,m)==1 for j in range(1,m+1))
        num=prod(Q(x**d-1,x**d)**mu(m//d) for d in D)
        assert Q(v,x**phi)==num>Q(1,4)
        assert 2*phi*phi>=m
        values[m,x]=v
        tests+=1

def small_prime(n):
    return n>1 and all(n%d for d in range(2,isqrt(n)+1))

same=[values[m,4] for m in (1,2,4,6,8,12,16)]
assert same==[3,5,17,13,257,241,65537] and all(map(small_prime,same))
multi=[values[m,x] for m,x in ((3,2),(3,3),(8,4))]
assert multi==[7,13,257] and all(map(small_prime,multi))
assert values[2,2]==values[6,2]==3
assert values[1,2]==1
for a in (2,3,4,5):
    widths=(a,a+1,a+2)
    index=(3,6,8)
    weights=(4,2,3)
    N=prod(values[m,x]**e for m,x,e in zip(index,widths,weights))
    E=sum(e*sum(gcd(j,m)==1 for j in range(1,m+1)) for m,e in zip(index,weights))
    assert E<=N.bit_length()+2*sum(weights)<=3*N.bit_length()
    if a>=3: assert (a-1)**E<=N<=(a+3)**E
    else: assert set(widths)<=set(range(2,5))
print("PASS cyclotomic algebra: %d exact values; two prime fixtures plus duplicates/units; four degree and boundary checks." % tests)
