"""Exact single-site harmonic cut; run next to higher_moments.py."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from math import isqrt, lcm
from flint import fmpq_mat
from higher_moments import rows, projections, SHIFTS, GRAM, dot, times
from rank36_three_types import UNIT


def possible(a,t):
    return (t >= 11*abs(a) and (t-a)%2 == 0 and not (a==0 and 0<t<14)
            and not (abs(a)==1 and t<=19) and not (abs(a)==2 and t==24))


def switch(z,n):
    a,t,k=z
    A,T,i=a+n, t+23*n*n+2*n*(7*k+2*a), k+3*n
    j=(A+4)//9
    return A-9*j, T-22*A*j+99*j*j, i+j


@cache
def orbit(z):
    seq=[switch(z,n) for n in range(-12,13)]
    seq += [(-a,t,-i) for a,t,i in seq]
    return min(seq,key=lambda z:(9*z[1]-11*z[0]**2,z))


@cache
def values(a,t):
    return tuple(k for k in range(-isqrt(t),isqrt(t)+1)
                 if 84*k*k+6*(4*k+2*a)**2+(3*k-9*a)**2<=84*t
                 and all(possible(*switch((a,t,k),n)[:2]) for n in range(-4,5)))


def admissible(z):
    for n in range(-5,6):
        a,t,k=switch(z,n)
        if not possible(a,t) or (t<100 and k not in values(a,t)):
            return False
    return True


@cache
def harmonic_coefficients(d):
    v=[Fraction(1)]
    for j in range(d//2):
        v.append(-v[-1]*Fraction((d-2*j)*(d-2*j-1),2*(j+1)*(48+2*d-2*j-4)))
    den=lcm(*(x.denominator for x in v))
    return tuple(int(den*x) for x in v)


def harmonic(d,ip,v2):
    return sum(c*ip**(d-2*j)*v2**j for j,c in enumerate(harmonic_coefficients(d)))


def main():
    raw=rows()
    shifts=[None,*SHIFTS]
    keys=sorted(set().union(*raw,*(projections(sh,n) for sh in shifts for n in (1,2,3))))
    atoms=set()
    by=defaultdict(list)
    for a,t in keys:
        for k in values(a,t):
            z=orbit((a,t,k))
            if admissible(z):
                atoms.add(z)
                by[a,t].append((k,z))
    atoms=sorted(atoms)
    ix={z:j for j,z in enumerate(atoms)}
    N=len(ix)
    def rr(k,n=0):
        r=[0]*N
        for i,z in by[k]:
            r[ix[z]]+=i**n
        return r
    def combine(d):
        return [sum(w*x for w,x in zip(d.values(),col)) for col in zip(*(rr(k) for k in d))]
    changes=[((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8)]
    matrix=[]
    def add(row,rhs=0):
        matrix.append(list(row)+[-rhs])
    for r in raw:
        w=dict(r)
        for target,source,mult in changes:
            w[source]=w.get(source,0)-mult*r.get(target,0)
        add(combine(w))
    for a,t in keys:
        k=a,t
        add([9*w+a*x for w,x in zip(rr(k,1),rr(k))])
        add([99*w-t*x for w,x in zip(rr(k,2),rr(k))])
    add(rr((0,0)),1)
    absence_start=len(matrix)
    absence_keys=sorted(UNIT-{(0,24),(1,27),(3,37)})
    for key in absence_keys:
        w={key:1}
        for target,source,mult in changes:
            if target==key:w[source]=-mult
        add(combine(w))
    def moment(sh,n,h,d):
        axis2=252+9*dot(h,times(GRAM,h))
        scale=1 if sh is None else 3
        acc=defaultdict(int)
        for (a,t),ws in projections(sh,n).items():
            weights=Counter((3//scale)*dot(w,h) for w in ws)
            for i,z in by[a,t]:
                v=sum(mult*harmonic(d,9*i+a+k,axis2*2*n) for k,mult in weights.items())
                acc[z]+=(2 if a else 1)*v
        return [acc[z] for z in atoms]
    for d in (2,4,6,8,10):
        for sh in shifts:
            for h in [(0,0,0,0),(1,2,3,1),(1,-1,1,-2)]:
                f,g,h3=[moment(sh,n,h,d) for n in (1,2,3)]
                if d==2:
                    add([y+48*x for x,y in zip(f,g)])
                    add([z+195804*x for x,z in zip(f,h3)])
                else:
                    c1,c2={4:(151740,192),6:(-99180,-552),8:(50220,432),10:(-22140,-312)}[d]
                    add([z-c1*x-c2*y for x,y,z in zip(f,g,h3)])
    e=[0]*N
    for z,w in [((-4,44,2),5940),((-4,46,-1),1650),((-4,48,2),2970),
                ((-1,23,-1),946),((-1,29,-1),220),((0,22,-1),1260)]:
        e[ix[z]]+=w
    for k,i,w in [((1,23),-1,627),((2,36),-2,165)]:
        e[ix[next(z for j,z in by[k] if i==j)]]+=w
    target=e+[-(14*627+7*165-70)]
    import json
    from pathlib import Path
    den,pairs=json.loads(Path(__file__).with_name("site-degree-ten-dual.json").read_text())
    assert den>0 and len(matrix)==282 and len(keys)==60 and N==172
    assert len(pairs)==len(dict(pairs))==164
    assert all(0<=j<len(matrix) and coef for j,coef in pairs)
    total=[sum(z*matrix[j][i] for j,z in pairs) for i in range(len(target))]
    assert total==[den*v for v in target]
    # Lift the 9 named unit rows instead of imposing them. Each is +V(k) on a graph.
    weights=dict(pairs)
    lift={k:3*Fraction(weights.get(absence_start+j,0),den) for j,k in enumerate(absence_keys)}
    assert lift=={(0,16):6120,(0,18):2940,(0,20):580,(0,26):300,(1,21):3420,
                  (1,25):600,(2,26):1920,(2,28):-920,(2,30):240}
    print("Exact site witness; 172 orbit columns; unconditional nine-family weights:",lift)


if __name__=="__main__":
    main()
