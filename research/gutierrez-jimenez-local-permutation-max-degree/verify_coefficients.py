#!/usr/bin/env python3
"""Check exact top coefficients with generating series, formal operators, and field sums."""
from itertools import product

if not __debug__:
    raise RuntimeError("Run without -O.")

class Field:
    """Integer coefficients in little-endian base p; monic moduli entered low-first."""
    def __init__(self,p,modulus=None):
        self.p=p
        self.mod=modulus
        self.r=len(modulus) if modulus else 1
        self.q=q=p**self.r
        self.coeff=[tuple((x//p**i)%p for i in range(self.r)) for x in range(q)]
        self.add=[[self.plus(a,b) for b in range(q)] for a in range(q)]
        self.mul=[[self.times(a,b) for b in range(q)] for a in range(q)]
        self.inv=[0]+[row.index(1) for row in self.mul[1:]]
        # Every nonzero element has a multiplication inverse, certifying the fields.
    def pack(self,c):
        return sum((z%self.p)*self.p**i for i,z in enumerate(c))
    def plus(self,a,b):
        return self.pack(x+y for x,y in zip(self.coeff[a],self.coeff[b]))
    def times(self,a,b):
        if not self.mod:
            return a*b%self.p
        c=[0]*(2*self.r-1)
        for i,x in enumerate(self.coeff[a]):
            for j,y in enumerate(self.coeff[b]):
                c[i+j]+=x*y
        for i in range(len(c)-1,self.r-1,-1):
            for j,z in enumerate(self.mod):
                c[i-self.r+j]-=c[i]*z
        return self.pack(c[:self.r])
    def pw(self,x,k):
        y=1
        while k:
            if k&1:
                y=self.mul[y][x]
            x=self.mul[x][x]
            k>>=1
        return y
    def total(self,seq):
        a=0
        for x in seq:
            a=self.add[a][x]
        return a

def sequence(p,r,N):
    num=[1,1]
    den=[1,3,-4]
    if r==1:
        h=(p-1)//2
        e=(-1)**h
        num+=[0]*h
        num[h]-=e
        num[h+1]-=e
        den+=[0]*h
        den[h+1]+=2*e
        den[h+2]+=8*e
    s=[]
    for j in range(N):
        t=num[j] if j<len(num) else 0
        t-=sum(den[d]*s[j-d] for d in range(1,min(j+1,len(den))))
        s.append(t%p)
    if r>1:
        assert s==[(2*j+1)%p if p==5 else ((3*pow(-4,j,p)+2)*pow(5,-1,p))%p for j in range(N)]
    return s

def formal(q,p,N):
    # Direct formal differentiation of g(t(X)) via the transposition indicator;
    # no paired spectrum or generating series used here.
    from math import comb
    g=[0,1]+[0]*(q-3)
    c=[]
    for _ in range(N):
        c.append(g[q-2])
        d=g[:]+[0]
        L=sum(g[1:])%p
        for j in range(q-1):
            d[j]=(d[j]+L*((-1)**(q-1-j))*comb(q-1,j))%p
        t=[0]*(q-1)
        for j in range(q-1):
            k=j-1
            if j>=1:
                e=q-1-k if k else 0
                t[e]=j*d[j]%p
        g=t
    return c

def table(F):
    def t(a):
        return 1-a if a in (0,1) else a
    return [[t(F.add[F.inv[a]][F.inv[b]]) for b in range(F.q)] for a in range(F.q)]

def move(F,T,dist,weights):
    z=[0]*F.q
    for a in range(F.q):
        if dist[a]:
            for b in range(F.q):
                j=T[a][b]
                z[j]=F.add[z[j]][F.mul[dist[a]][weights[b]]]
    return z

def evaluate(F,dist,n):
    c=F.total(F.mul[x][w] for x,w in enumerate(dist))
    return F.mul[F.p-1][c] if n%2 else c

def moment(F,T,orders):
    weights={j:[F.pw(a,j) for a in range(F.q)] for j in set(orders)}
    dist=weights[orders[0]][:]
    for j in orders[1:]:
        dist=move(F,T,dist,weights[j])
    return evaluate(F,dist,len(orders))

def grid(F,T,orders):
    # Literal product grid, independent of state aggregation.
    def term(x):
        y=x[0]
        for v in x[1:]:
            y=T[y][v]
        for v,p in zip(x,orders):
            y=F.mul[y][F.pw(v,p)]
        return y
    c=F.total(term(x) for x in product(range(F.q), repeat=len(orders)))
    return F.mul[F.p-1][c] if len(orders)%2 else c

def main():
    fields=[(p,None) for p in (5,7,11,13,17,19,23,29,31)]
    fields += [(3,(1,0)), (3,(2,2,0)), (5,(3,0)), (5,(1,1,0)), (7,(4,0))]
    for p,mod in fields:
        F=Field(p,mod)
        S=sequence(p,F.r,60)
        expected=[0]+[a for s in S for a in (2*s%p,-4*s%p)]
        assert formal(F.q,p,len(expected))==expected
        T=table(F)
        dist=list(range(F.q))
        for n,c in enumerate(expected[:45],1):
            assert evaluate(F,dist,n)==c
            dist=move(F,T,dist,list(range(F.q)))
        assert expected[1:5]==[z%p for z in (2,-4,-4,8)]
    print(f"generating series = direct formal differentiation (121 arities) = field moments (45 arities), {len(fields)} fields")
    for p,M,n,j,e,value in ((5,(3,0),6,5,137,1),(19,None,8,1,135,18),(7,None,10,1,49,3)):
        F=Field(p,M); T=table(F)
        assert moment(F,T,[1]*n)==0
        ks=[1]*n;ks[j-1]=2
        assert moment(F,T,ks)==value
        assert e==n*(F.q-2)-1
        print(f"q={F.q}, n={n}: top=0; x_{j} alone one exponent lower gives {value}; exact degree {e}")
    for p,M,n in ((5,None,6),(7,None,5),(3,(1,0),4)):
        F=Field(p,M); T=table(F)
        for ks in ([1]*n,[2]+[1]*(n-1)):
            assert grid(F,T,ks)==moment(F,T,ks)
        print(f"q={F.q}, n={n}: literal grid of {F.q**n} inputs agrees for two monomials")
    print("PASS coefficient and counterexample verification")

if __name__=="__main__":
    main()
