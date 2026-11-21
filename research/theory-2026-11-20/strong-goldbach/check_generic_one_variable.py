#!/usr/bin/env python3
from itertools import product
from math import isqrt
def ck(x,msg):
    if not x:raise ValueError(msg)
def isp(n):return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def mod_wit(t,r,l,d):
    if l==3:
        a=[t]*d
    elif l==2:a=[1]*d
    else:
        a=[]
        for i in range(d):
            bad={0,2*t%l}
            if i==1:bad.add(((r if d==2 else 3)-a[0])%l)
            if i==3:bad.update(((3-a[2])%l,(r+6-sum(a))%l))
            a.append(next(i for i in range(l) if i not in bad))
    extra=[sum(a)-r] if d==2 else [sum(a[:2])-3,sum(a[2:])-3,sum(a)-6-r]
    return all(k%l for k in [t,*a,*[2*t-i for i in a],*extra])
def actual(t,r):
    d=4 if r%3==(-t)%3 else 2
    aa=[a for a in range(3,2*t,2) if isp(a) and isp(2*t-a)]
    if d==2:
        for a,b in product(aa,repeat=2):
            if isp(a+b-r):return d,[a,b],[a+b-r]
    else:
        c={a+b-3:(a,b) for a,b in product(aa,repeat=2) if isp(a+b-3)}
        for s,h in product(c,repeat=2):
            if isp(s+h-r):return d,c[s]+c[h],[s,h,s+h-r]
    raise RuntimeError('no example')
def main():
    n=0
    for tmod in (1,2):
        for rmod in (0,1,2):
            d=4 if rmod==(-tmod)%3 else 2
            for l in [2,3,5,7,11,13,17,19,23,29,31]:
                for t in ([tmod] if l==3 else range(1,l)):
                    for r in ([rmod] if l==3 else [1] if l==2 else range(l)):
                        ck(mod_wit(t,r,l,d),'mod obstruction');n+=1
    print('conditional local fixtures:',n)
    for t,r in [(1009,3),(1009,7),(1009,5),(1013,7),(1013,5)]:
        d,a,z=actual(t,r)
        ck(all(isp(p) for p in (t,r,*a,*[2*t-n for n in a],*z)),'not primes')
        if d==2:ck(a[0]+a[1]==r+z[0],'short move')
        else:ck(a[0]+a[1]==3+z[0] and a[2]+a[3]==3+z[1] and z[0]+z[1]==r+z[2],'long move')
        print('literal unit moves t,r,d,a,aux:',t,r,d,a,z)
    print('PASS')
if __name__=='__main__':main()
