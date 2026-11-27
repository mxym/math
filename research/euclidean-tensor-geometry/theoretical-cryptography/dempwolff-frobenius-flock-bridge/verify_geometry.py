"""Second check: positive lifts by their actual outer slices; negative by unrestricted local equations."""
from itertools import combinations
from math import gcd

POLYS = [7,11,19,37,67,131,285,529,1033]


def need(ok, msg):
    if not ok:
        raise ValueError(msg)


class Field:
    def __init__(self, n, f):
        self.q = q = 1<<n
        # Use the reciprocal modulus to change the basis, then independently
        # build a full multiplicative log table by polynomial long division.
        mod = int(f'{f:0{n+1}b}'[::-1],2)
        def product(a,b):
            r=0
            for j in range(n):
                if b>>j&1: r ^= a<<j
            while r>=q: r ^= mod<<(r.bit_length()-n-1)
            return r
        for g in range(2,q):
            p=[1]
            while True:
                z=product(p[-1],g)
                if z==1: break
                need(0<z<q and len(p)<q,'invalid modulus or generator')
                p.append(z)
            if len(p)==q-1: break
        need(len(p)==q-1, 'no generator')
        self.p=p; self.log={x:i for i,x in enumerate(p)}
        self.tr=[sum((self.mul(x,1<<j)>>j)&1 for j in range(n))&1
                 for x in range(q)]
    def mul(self,a,b):
        return self.p[(self.log[a]+self.log[b])%(self.q-1)] if a and b else 0
    def power(self,a,e):
        if not a:
            need(e>0,'invalid power at zero')
            return 0
        return self.p[(self.log[a]*e)%(self.q-1)]


def visit(n,f,k):
    # Delta in the arbitrary outer offsets' first coordinates. Directly
    # solve b*x^(2^k)+c*x^(2^k)=delta (second coordinates equal).
    # Return 1 when the two trace coordinates DISAGREE, avoiding collision.
    q=f.q
    inv={d:f.power(d,q-2) for d in range(1,q)}
    root=[f.power(x,1<<(n-k)) for x in range(q)]
    def avoidance(j,delta):
        x=root[f.mul(delta,inv[j])]
        return f.tr[f.mul(j,x)]
    if n-k<=2:
        scale=1 if n-k==2 else f.tr.index(1)
        a=[0]+[f.mul(scale,f.power(x,q-(1<<k))) for x in range(1,q)]
        for b,c in combinations(range(q),2):
            need(avoidance(b^c,a[b]^a[c]), 'colliding explicit pair')
        # All finite outer representatives have z=1,y=0, so no collision
        # with the outside coset of U_infty (which has z=0,y=0).
        return f'yes:{q*(q-1)//2}'

    # No averaging or cyclic-word argument: allow independent n-bit
    # variables a_b on each selected label. An inconsistent subsystem
    # suffices; the returned number of labels is an upper bound on its support.
    labels=range(min(q,96))
    coeffs={d:sum(avoidance(d,1<<i)<<i for i in range(n))
            for d in range(1,q)}
    pivots={}
    for c in labels:
        for b in range(c):
            s=coeffs[b^c]
            r=s<<((c-1)*n+1)
            if b:
                r ^= s<<((b-1)*n+1)
            r |= 1 # right hand side of the equation
            while r>1:
                lead=r.bit_length()-1
                if lead not in pivots:
                    pivots[lead]=r
                    break
                r ^= pivots[lead]
            if r==1:
                return f'no:{c+1}'
    raise ValueError(f'no geometric obstruction found, n={n} k={k}')


if __name__=='__main__':
    for n,mod in enumerate(POLYS,2):
        field=Field(n,mod)
        results=' '.join(f'{k}={visit(n,field,k)}' for k in range(1,n) if gcd(k,n)==1)
        print(f'n={n} {results}')
