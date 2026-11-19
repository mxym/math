"""Independent integer/CDF check: finite parent maps and a Kesten-tree stochastic enclosure.
No nonstandard dependencies; no floats or assertions. No inputs from the original verifier.
Run python3 -O independent.py.
"""
from fractions import Fraction as F
from itertools import product, accumulate
from math import factorial

def require(x):
    if not x: raise ArithmeticError('failed independent verification')

def enum_maps(n):
    costs=(F(1,2),F(1),F(3,2))
    tables={}; ntrees=0; tree_checks=0; lip_checks=0
    for p in product(range(n),repeat=n-1):
        es=[(j,i) for j,i in enumerate(p,1)]
        allowed=[a for a in range(1<<n) if all(not ((a>>j)&(a>>i)&1) for j,i in es)]
        mult=[sum(m.bit_count()==k for m in allowed) for k in range(n+1)]
        vals=tuple(sum(x**k*c for k,c in enumerate(mult)) for x in costs)
        tables[p]=vals
        reachable={0}
        for _ in range(n): reachable.update(j for j,i in es if i in reachable)
        if len(reachable)!=n:continue
        ntrees+=1
        # Compose exact in/out odds and their derivative in log-activity.
        def visit(v,x):
            z=F(1); r=x; deriv=F(1); tally=F(0)
            for w,i in es:
                if i==v:
                    u,du,zw,dt=visit(w,x)
                    r/=1+u; deriv-=u*du/(1+u); z*=zw; tally+=dt
            return r,deriv,z*(1+r),tally+r*deriv/(1+r)
        for u,x in enumerate(costs):
            r,dr,z,dz=visit(0,x)
            occ=sum(x**m.bit_count() for m in allowed if m&1)
            size_tot=sum(k*v*x**k for k,v in enumerate(mult))
            require(z==vals[u] and dz*z==size_tot and z*r/(1+r)==occ)
            tree_checks+=1
    require(ntrees==n**(n-2))
    for p,v in tables.items():
        for j in range(n-1):
            for i in range(p[j]+1,n):
                w=tables[p[:j]+(i,)+p[j+1:]]
                for z1,z2,x in zip(v,w,costs):
                    require(max(z1,z2)<=(1+x)*min(z1,z2));lip_checks+=1
    return (len(tables),ntrees,tree_checks,lip_checks)

K=512; M=2**43; D=11; HEIGHT=14
def cdf_to_law(c):
    require(c[-1]==M and all(0<=a<=b for a,b in zip([0]+c[:-1],c)))
    return [v-o for v,o in zip(c,[0]+c[:-1])]
def round_count(num,den,lower):
    # A law stochastically BELOW the true one is characterized by a LARGER CDF.
    return (num+den-1)//den if lower else num//den
def point(i):return [M if j==i else 0 for j in range(K+1)]
def cdf_div(X,Y,below):
    # Event floor(i K/(K+j))<=r is i K < (r+1)(K+j);
    # event ceil(i K/(K+j))<=r is i K <=r(K+j).
    # Sum probabilities conditionally on j; no binning of each (i,j) outcome.
    F0=list(accumulate(X));nz=[(j+K,q) for j,q in enumerate(Y) if q]
    c=[]
    for r in range(K):
        if below:
            num=sum(q*F0[min(K,((r+1)*j-1)//K)] for j,q in nz)
        else:
            num=sum(q*F0[min(K,(r*j)//K)] for j,q in nz)
        c.append(round_count(num,M,below))
    return cdf_to_law(c+[M])

# e <= sum_{j=0}^17 1/j! + (1/18!)/(1-1/19), by term-ratio.
Elower=1/(sum((F(1,factorial(j)) for j in range(18)),F(0))+F(19,18*factorial(18)))
pn=[Elower/factorial(d) for d in range(D+1)]
require(0<sum(pn)<1)
def mix_product(child,below):
    q=point(K); co=[] 
    for h in range(D+1):
        co.append(list(accumulate(q)))
        if h!=D:q=cdf_div(q,child,below)
    missing=M*(1-sum(pn)) if below else F(0)
    # Truncated degree distribution plus mass bounded by the appropriate endpoint.
    cf=[]
    for r in range(K):
        exact=missing+sum(w*c[r] for w,c in zip(pn,co))
        cf.append(round_count(exact.numerator,exact.denominator,below))
    return cdf_to_law(cf+[M])
def occupation(x):return sum((F(p*i,M*(K+i)) for i,p in enumerate(x)),F(0))
def kesten():
    lower,upper=point(0),point(K)
    las,uas=lower,upper
    for h in range(HEIGHT):
        lower,upper=mix_product(upper,True),mix_product(lower,False)
        las,uas=cdf_div(lower,uas,True),cdf_div(upper,las,False)
        require(all(x>=y for x,y in zip(accumulate(las),accumulate(uas))))
    a,b=occupation(las),occupation(uas)
    u,v=a*10**6,b*10**6
    print(f'Kesten enclosure using alternative CDF rounding, K={K}, M={M}, degree through {D}, height {HEIGHT}:',u.numerator//u.denominator,-(-v.numerator//v.denominator))
    require(F(304684,10**6)<=a<=b<=F(307543,10**6))

if __name__=='__main__':
    results=[enum_maps(n) for n in range(2,7)]
    print('n=2..6 map counts / admissible trees / exact tree-and-activity checks / coordinate-activity checks:',results)
    kesten()
    print('PASS')
