"""Exact finite tests for qutrit pair rigidity. Standard Python; -O is OK."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product

def check(x):
    if not x:
        raise ArithmeticError('exact check failed')

# Eisenstein integers a+b*w with w^2+w+1=0.
zero=(0,0); one=(1,0); w=(0,1)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def times(k,x): return (k*x[0], k*x[1])
def mul(x,y):
    a,b=x; c,d=y
    return (a*c-b*d, a*d+b*c-b*d)
def bar(x): return (x[0]-x[1],-x[1])
def norm(x): a,b=x; return a*a-a*b+b*b
def dot(x,y):
    s=zero
    for a,b in zip(x,y):
        s=add(s,mul(a,b))
    return s
def mm(A,B): return [[dot(row,col) for col in zip(*B)] for row in A]
def ident(d): return [[(d if i==j else 0,0) for j in range(3)] for i in range(3)]
def rot(i,j,c,s,d):
    check(c*c+s*s==d*d)
    a=ident(d); a[i][i]=a[j][j]=(c,0);a[i][j]=(-s,0);a[j][i]=(s,0)
    return a
def unitary(A,d):
    for i,j in product(range(3),repeat=2):
        check(dot(A[i],[bar(x) for x in A[j]])==(d*d if i==j else 0,0))
def coarses():
    for i,j in [(0,1),(0,2),(1,2)]:
        for c,s,d in [(3,4,5),(5,-12,13)]:
            yield rot(i,j,c,s,d),d
def phasegrid():
    roots=[one,w,mul(w,w),neg(one),neg(w),neg(mul(w,w))]
    return [(mul(r,mul(z,z)),norm(z)) for z in [one,(3,1),(5,-2)] for r in roots]

def test_rows():
    n=0
    for a,b,c in product(range(8),repeat=3):
        if sum(x>0 for x in (a,b,c))<2:continue
        products=(a*b,b*c,c*a); small=products.index(min(products))
        signs=tuple(1 if j==small else -1 for j in range(3))
        u,v=signs[0],signs[2];check(u*v==signs[1])
        D=sum(p*s for p,s in zip(products,signs));check(D<0)
        vals=[]
        for r in [one,w,mul(w,w)]:
            s=add((a,0),add(times(u*b,r),times(v*c,mul(r,r))))
            vals.append(norm(s)-a*a-b*b-c*c)
        check(vals==[2*D,-D,-D]);n+=1
    return n

def test_pairs():
    phases=phasegrid();I=ident(1); X=ident(1);X[1][1]=w
    base=list(coarses());cases=[(I,1)]+base
    for (A,d),(B,e) in product(base,repeat=2):
        for K in [I,X]:
            D=mm(mm(A,K),B);cases.append((D,d*e))
            for C,f in base[::2]:cases.append((mm(D,C), d*e*f))
    profiles={}; total=0
    for A,d in cases:
        unitary(A,d)
        monomial=any(norm(x)==d*d for row in A for x in row)
        nz=sum(x==zero for row in A for x in row)
        found=False
        for (u,du),(v,dv) in product(phases,repeat=2):
            bound=(d*du*dv)**2
            vec=[(du*dv,0),times(dv,u),times(du,v)]
            vals=[norm(dot(row,vec)) for row in A]
            check(sum(vals)==3*bound);total+=1
            if sum(x>bound for x in vals)>=2:found=True;break
        check(found != monomial)
        profiles[nz]=profiles.get(nz,0)+1
    # Fourier differs by a common factor 1/sqrt(3).
    four=[[mul(one,[one,w,mul(w,w)][i*j%3]) for j in range(3)] for i in range(3)]
    check([norm(dot(row,[one,one,neg(one)])) for row in four]==[1,4,4])
    return profiles,total

def test_cutoff():
    # All unordered mixtures of 1--4 equally-weighted outcomes from
    # single-basis probability lists on the grid 0,1/6,...,1.
    triples=set(tuple(sorted((a,b,6-a-b))) for a in range(7) for b in range(7-a))
    count=0
    for n in range(1,5):
        for rows in combinations_with_replacement(sorted(triples),n):
            pool=sorted(x for row in rows for x in row)
            target=sum(pool[-n:]);alpha=sum(max(row) for row in rows)
            check(target>=alpha)
            values=[n*t+sum(max(0,x-t) for x in pool) for t in range(7)]
            check(min(values)==target)
            for t in range(7):
                z=sum(max(0,t-c)+max(0,b-t)+max(0,a-t) for a,b,c in rows)
                check(z==values[t]-alpha)
            count+=1
    check(F(3,3)-F(3,6)+F(1,9)==F(11,18))
    check((3*F(11,18)-1)/2==F(5,12))
    return count
if __name__=='__main__':
    print(f'PASS {test_rows()} sign-orbit row witnesses (including vanishing coefficients).')
    profiles,total=test_pairs()
    print(f'PASS rational complex unitaries by number of zero entries: {dict(sorted(profiles.items()))}; {total} exact torus probes; exact Fourier (1,4,4)/9.')
    print(f'PASS {test_cutoff()} pure finite pooling lists / all integral cutoffs, ties and common-cutoff equality.')
