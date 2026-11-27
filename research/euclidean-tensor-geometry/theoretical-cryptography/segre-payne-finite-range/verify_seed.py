"""Verify the field, primitive generator, and local rigidity over the binary field."""
from functools import cache
from pathlib import Path
import json, math, sys


def check(ok, msg):
    if not ok:
        raise ValueError(msg)


def pm(a, b):
    while a and a.bit_length()>=b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def pgcd(x,y):
    while y:
        x,y=y,pm(x,y)
    return x


class GF:
    def __init__(self, n, modulus):
        self.n=n; self.q=1<<n; self.f=modulus
        check(modulus.bit_length()==n+1 and modulus&1,'modulus')
    def mul(self,a,b):
        out=0
        while b:
            i=b&-b
            out^=a<<(i.bit_length()-1); b-=i
        return pm(out,self.f)
    def power(self,x,k):
        p=1
        while k:
            if k&1:p=self.mul(p,x)
            x=self.mul(x,x)
            k>>=1
        return p
    def trace(self,x):
        r=0
        for _ in range(self.n):
            r ^= x
            x=self.mul(x,x)
        check(r in (0,1),'trace not binary')
        return r
    def is_field(self):
        # An n-th degree polynomial is irreducible iff it divides X^(2^n)-X
        # and has no irreducible factor of degree at most n//2.
        x=2
        for i in range(1,self.n+1):
            x=self.mul(x,x)
            if i<=self.n//2 and pgcd(x^2,self.f)!=1:return False
        return x==2
    def primitive(self, primes):
        N=self.q-1
        return self.power(2,N)==1 and all(self.power(2,N//p)!=1 for p in primes)


def prime_verifier(doc):
    @cache
    def test(p):
        if p==2:return True
        data=doc.get(str(p))
        if data is None:return False
        g,fac=data
        if not (1<g<p and all(1<r<p and test(r) for r in fac) and math.prod(fac)==p-1):
            return False
        # g mod p has exact order p-1; therefore its group of units has at
        # least p-1 elements, forcing p to be prime.
        return pow(g,p-1,p)==1 and all(pow(g,(p-1)//r,p)!=1 for r in set(fac))
    return test


def row_masks(f,L):
    n=f.n
    # mul(z^i,v) for i<n; obtain all trace coefficients of v using the
    # trace functional in the polynomial basis.
    trmask=sum(f.trace(1<<i)<<i for i in range(n))
    def mask(v):
        r=0
        for i in range(n):
            r |= ((trmask&v).bit_count()&1)<<i
            v<<=1
            if v>=f.q:v^=f.f
        return r
    # For x=g^(j+d), y=g^j, write Z(x)=H(x)/x^5.
    # Equation: Tr(D_d (g^(5d) Z(x)+Z(y)))=0 with
    # D_d=(1+g^d)/(1+g^(6d)).
    left=[]; right=[]
    for d in range(1,L):
        x=f.power(2,d); denom=1^f.power(x,6)
        check(denom!=0,'repeated seed label')
        v=f.mul(1^x,f.power(denom,f.q-2))
        left.append(mask(f.mul(v,f.power(x,5))))
        right.append(mask(v))
    return trmask,left,right


def seed_rank(f,L):
    n=f.n
    one,left,right=row_masks(f,L)
    # For the particular solution G0=x^5, its scaled values are constant 1.
    # Every pair class must return 1, including the separate row against 0.
    check((one&1)==1 and all(((a^b)&1)==1 for a,b in zip(left,right)),
          'Payne RHS on seed')
    # Check the known n basis functions on every difference class, using the
    # actual row bitmasks. Passing from (g^d,1) to (g^(d+j),g^j) replaces
    # C by g^(-2j) C in the Z-coordinate formula: this still runs over F.
    basis=[1<<i for i in range(n)]
    square=[f.mul(c,c) for c in basis]
    def zvec(x):
        u=f.power(x,f.q-3) # x^(-2)
        u2=f.mul(u,u)
        return [f.mul(a,u2)^f.mul(b,u) for a,b in zip(square,basis)]
    z1=zvec(1)
    check(all(not ((one&z).bit_count()&1) for z in z1),'pair with zero')
    for d,(a,b) in enumerate(zip(left,right),1):
        zr=zvec(f.power(2,d))
        for z,w in zip(zr,z1):
            check(not (((a&z).bit_count()+(b&w).bit_count())&1),'gauge row')
    # Consecutive windows overlap at g and g^2. Check C is injected into
    # this two-value restriction by elimination on the actual basis images.
    images=[u|(v<<n) for u,v in zip(zvec(2),zvec(f.mul(2,2)))]
    pairpiv={}
    for w in images:
        while w:
            b=w.bit_length()-1
            if b not in pairpiv:
                pairpiv[b]=w
                break
            w^=pairpiv[b]
    check(len(pairpiv)==n,'two-point injectivity')
    piv={}
    def add(r):
        while r:
            k=r.bit_length()-1
            old=piv.get(k)
            if old is None:
                piv[k]=r
                return
            r^=old
    for i in range(L):
        add(one<<(n*i))
        for j in range(i):
            add((left[i-j-1]<<(n*i))^(right[i-j-1]<<(n*j)))
    return len(piv)


def main():
    data=json.loads(Path(__file__).with_name('fields.json').read_text())
    prime=prime_verifier(data['primes'])
    requested=set(map(int,sys.argv[1:]))
    ns=[row[0] for row in data['fields']]
    check(ns==list(range(3,128,2)) and requested<=set(ns), 'parameter coverage')
    for n,mod,factors,L in data['fields']:
        if requested and n not in requested:continue
        f=GF(n,mod)
        check(math.prod(factors)==f.q-1 and all(prime(p) for p in factors), 'factor certificates')
        check(f.is_field() and f.primitive(set(factors)), 'field / primitive generator')
        check(3<=L<=f.q-1,'seed size')
        rank=seed_rank(f,L)
        check(rank==n*(L-1),'seed not rigid')
        print(f'n={n} L={L} rank={rank} kernel={n} PASS',flush=True)


if __name__=='__main__':main()
