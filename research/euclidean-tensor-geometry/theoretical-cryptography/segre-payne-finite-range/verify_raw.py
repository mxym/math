"""Independent seed-rank verification: reciprocal field model, direct unscaled rows."""
import json, pathlib, sys


def demand(b,s):
    if not b: raise ArithmeticError(s)


class Field:
    def __init__(self,n,mod):
        self.n=n
        self.q=1<<n
        self.f=int(bin(mod)[2:][::-1],2)
        demand(self.f.bit_length()==n+1,'wrong reciprocal degree')
    def shift(self,x):
        return (x<<1)^ (self.f if x>>(self.n-1) else 0)
    def product(self,x,y):
        z=0
        while y:
            if y&1:z^=x
            x=self.shift(x)
            y>>=1
        return z
    def inv(self,a):
        demand(bool(a),'division by zero')
        u,v,s,t=a,self.f,1,0
        while u!=1:
            demand(bool(u),'reducible modulus')
            off=u.bit_length()-v.bit_length()
            if off<0:
                u,v=v,u; s,t=t,s
                off=-off
            u^=v<<off; s^=t<<off
        while s.bit_length()>self.n:s^=self.f<<(s.bit_length()-self.n-1)
        return s
    def sixth(self,x):
        u=self.product(x,self.product(x,x))
        return self.product(u,u)
    def mask(self,x):
        # Replace Tr by the nonzero coefficient functional [z^(n-1)];
        # they differ by an invertible common scaling of each unknown.
        out=0
        for j in range(self.n):
            out^=(x>>(self.n-1))<<j
            x=self.shift(x)
        return out
    def power(self,x,k):
        v=1
        for c in bin(k)[2:]:
            v=self.product(v,v)
            if c=='1':v=self.product(v,x)
        return v


def run(n,mod,primes,L):
    f=Field(n,mod)
    N=f.q-1
    # In a ring of size 2^n, an element of order 2^n-1 accounts for every
    # nonzero element. This verifies our reciprocal construction is a field;
    # primality of the supplied factorizations is certified by verify_seed.py.
    demand(f.power(2,N)==1 and all(f.power(2,N//p)!=1 for p in set(primes)), 'not primitive')
    labels=[1]
    for _ in range(L-1):labels.append(f.shift(labels[-1]))
    labels=[0]+labels
    sixth=[f.sixth(x) for x in labels]
    piv={}
    def add(x):
        while x:
            j=x.bit_length()-1
            y=piv.setdefault(j,x)
            if y==x:return
            x^=y
    for j in range(1,len(labels)):
        for i in range(j-1,-1,-1):
            # F-variables are the values H at the original x. No scaled Z,
            # cyclic rows, precomputed ratios, or additive-coordinate trace.
            w=f.product(labels[i]^labels[j],f.inv(sixth[i]^sixth[j]))
            m=f.mask(w)
            row=m<<((j-1)*n)
            if i:row ^= m<<((i-1)*n)
            add(row)
    target=(L-1)*n
    demand(len(piv)==target,'raw rank %d != %d'%(len(piv),target))
    print(f'n={n} raw-rank={len(piv)} nullity={L*n-len(piv)} OK',flush=True)


if __name__=='__main__':
    rows=json.loads(pathlib.Path(__file__).with_name('fields.json').read_text())['fields']
    requested={int(k) for k in sys.argv[1:]}
    ns=[row[0] for row in rows]
    demand(ns==list(range(3,128,2)) and requested<=set(ns),'parameter coverage')
    for row in rows:
        if not requested or row[0] in requested:run(*row)
