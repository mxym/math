"""Exact replay for local roots, signed endpoints and physical odd centering."""
from fractions import Fraction as F
from itertools import product
from math import prod


def need(ok, info):
    if not ok:
        raise ArithmeticError(info)


ps = [2, 3, 5, 7, 11, 13, 17, 23, 31, 47]
checks = 0
for p in ps:
    for n in range(0, p, 2 if p == 2 else 1):
        allowed = set(range(1, p)) - {n}
        k = len(allowed)
        s = F(p*k, (p-1)**2)
        d = F(p*k*(k-1), (p-1)**3)
        rho = F(k, p-1)
        need((1-F(1,p))*d+s/p == rho*rho, ('first factor', p, n))
        if d:
            lam = s/d-1
            need(lam >= 0 and d*(1+lam)==s, ('positive lambda', p, n))
            need(lam/(1+lam) == F(p-k, p-1) <= F(2,p-1), ('inclusion',p,n))
        else:
            need(k == 1 and p in (2,3), ('forced moduli',p,n))
        for sign in (-1, +1):
            tgt = n if sign == +1 else 0
            counts = [0]*p
            for a in allowed:
                for b in allowed:
                    for inv_r in range(1,p):
                        # Each unit-modulus value r corresponds bijectively to inv_r.
                        counts[((a+sign*b-tgt)*inv_r)%p] += 1
            for h,got in enumerate(counts):
                need(F(p*got,(p-1)**3) == (s if h==0 else d), ('local count',p,n,h,sign))
                checks += 1


def tent(t):
    return max(F(0),1-abs(t))


def delta_mesh(t):
    m = int(1/t)
    return 2*m - t*m*(m+1) - 1/t


endpoint_checks = 0
for n in range(2, 50, 2):
    finite = [2,3,5,7,11]
    rows = []
    for p in finite:
        k = p-(1 if n%p==0 else 2)
        rows.append((p,F(p*k,(p-1)**2),F(p*k*(k-1),(p-1)**3),F(k,p-1)))
    m0=prod(p for p,s,d,r in rows if not d)
    C=prod(d if d else s for p,s,d,r in rows)
    allowed=[(p,s/d-1) for p,s,d,r in rows if d]
    coeff=[(prod(p for (p,_),bit in zip(allowed,bits) if bit),
            prod((lam for (_,lam),bit in zip(allowed,bits) if bit), start=F(1)))
           for bits in product((False,True), repeat=len(allowed))]
    EA=C*sum(lam for d,lam in coeff)
    PA=C/m0*sum(lam/d for d,lam in coeff)
    need(EA==prod(s for p,s,d,r in rows), ('second Euler product',n))
    need(PA==prod(r*r for p,s,d,r in rows), ('first Euler product',n))
    for v in [F(1,9),F(2,83),F(1,325),F(3,1011)]:
        literal=2*sum(prod(s if h%p==0 else d for p,s,d,r in rows)*tent(v*h)
                      for h in range(1,int(1/v)+1))
        priced=C*sum(lam*delta_mesh(m0*d*v) for d,lam in coeff)
        need(-EA<=priced<=0 and literal==PA/v+priced, ('literal signed endpoint',n,v))
        endpoint_checks += 1

ap_checks=0
data={19:11,23:13,29:17,31:19,37:12,41:17,43:6,47:11}
A=sum(data.values())
for q in [3,5,7,11,13,17]:
    e=[F(0)]+[sum(c for p,c in data.items() if p%q==a)-F(A,q-1) for a in range(1,q)]
    for n in range(36, 100, 2):
        gam=sum(e[a]*e[(n-a)%q] for a in range(q))
        var=sum(e[a]**2 for a in range(q))
        odd=sum(((e[a]-e[(n-a)%q])/2)**2 for a in range(q))
        need(2*odd==var-gam, ('odd physical centering',q,n))
        ap_checks += 1
print(f'PASS: {checks} true local affine counts, {endpoint_checks} signed endpoints, '
      f'{ap_checks} odd-projection replays')
