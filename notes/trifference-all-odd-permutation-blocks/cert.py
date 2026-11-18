"""Two exact counts of bad ordered triples in a finite inner block. No dependencies."""
from itertools import combinations, permutations, product
from math import comb, factorial, log2
from fractions import Fraction
from functools import lru_cache

def need(v, msg):
    if not v: raise ArithmeticError(msg)
def sizes(q,n):
    counts=[0]*(q+1); counts[0]=1
    for _ in range(n):
        new=[0]*(q+1)
        for i,val in enumerate(counts):
            if i: new[i-1]+=i*val
            if i<q: new[i+1]+=(q-i)*val
        counts=new
    return counts[q]

def fourier(q,n):
    total=0
    fac=factorial(q)
    points=range(q+7)
    tab=[[(-1)**((s&m).bit_count()) for s in range(8)] for m in range(8)]
    for cuts in combinations(points,7):
        c=[b-a-1 for a,b in zip((-1,)+cuts,cuts+(q+7,))]
        ways=fac
        for x in c: ways//=factorial(x)
        z=[sum(a*b for a,b in zip(c,row)) for row in tab]
        h=z[3]*z[4]+z[5]*z[2]+z[6]*z[1]-2*z[7]
        sign=(-1)**sum(c[s]*s.bit_count() for s in range(8))
        total+=ways*sign*h**n
    a,b=divmod(total,2**(3*q))
    need(b==0,'Fourier divisibility')
    return a

@lru_cache(None)
def transitions(c):
    d={}
    def add(u,w):
        u=tuple(u)
        d[u]=d.get(u,0)+w
    for i,ci in enumerate(c):
        if not ci: continue
        v=list(c);v[i]-=1;v[i^7]+=1;add(v,ci)
        for j,cj in enumerate(c):
            m=cj-int(i==j)
            if not m: continue
            for a,b in ((3,4),(5,2),(6,1)):
                v=list(c);v[i]-=1;v[j]-=1;v[i^a]+=1;v[j^b]+=1
                add(v,ci*m)
    return d

def dp(q,n):
    start=(q,)+(0,)*7; end=(0,)*7+(q,)
    D={start:1}
    for i in range(n):
        E={}
        for c,w in D.items():
            for s,t in transitions(c).items():
                E[s]=E.get(s,0)+w*t
        D=E
        need(sum(D.values())==(q*(3*q-2))**(i+1),'transition mass')
    return D.get(end,0)

def pperm(q):
    return sum(Fraction((-2)**j*comb(q-j+2,2),factorial(j)) for j in range(q+1))/factorial(q)

def permcheck(q):
    ps=list(permutations(range(q))); ident=tuple(range(q))
    b=sum(all(len({i,x,y})<3 for i,x,y in zip(ident,s,t)) for s in ps for t in ps)
    need(Fraction(b,len(ps)**2)==pperm(q),'permutation class count')

if __name__=='__main__':
    for q in range(2,7):permcheck(q)
    for q,n in ((3,3),(3,5),(4,6),(5,7),(9,11)):
        a=sizes(q,n); b=fourier(q,n); c=dp(q,n)
        need(b==c and a>0,'two independent integer enumerations')
        if n==q+2:need(a==q*factorial(n)//6,'explicit inner size')
        print(q,n,a,b)
    f=Fraction(b,a**3)
    need((a,b)==(59875200,458769821652172800) and f==Fraction(5441833,2546192880000),'advertised nine-letter certificate')
    # 0.21404=5351/25000; compare -log2(f)/88 without rounding.
    need(f.denominator**25000>2**(88*5351)*f.numerator**25000,'rate >0.21404')
    # Reproduce the exact comparison with the November 12 bound (length 14).
    y=Fraction(25,81)**14*(1-4*Fraction(7,9)**14+3*Fraction(161,225)**14)/(1-Fraction(7,9)**14)**3
    need(f**14 < y**11,'strict comparison with Yuan–Zhu')
    print('F =',f,'rate =',-log2(f)/88)
