"""Exact finite controls for cancellation, CRT locals, and the least-bit pairing.
The uniform analytic and all-rank inequalities are proved in Proof.md."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import prod
from pathlib import Path
def check(x,why):
    if not x: raise ValueError(why)
def subsets(x):
    e=[(0,1)]
    for a in x:
        e += [(s+a,-v) for s,v in e]
    return e
def ramp(s):
    # Compact C^2 flat-top rational control, not the proof's small-slope choice.
    if s<=F(1,16):return F(1)
    if s>=F(1,4):return F(0)
    t=(16*s-1)/3
    return 1-10*t**3+15*t**4-6*t**5
def cases():
    n=0
    for k in range(2,8):
      for x in combinations_with_replacement((1,3,9,27,81),k):
       for y in set(x):
        a0=x[0]
        e=subsets(x)
        raw=sum(v*ramp(F(s,y)) for s,v in e)
        e0=subsets(x[1:])
        alt=sum(v*(ramp(F(s,y))-ramp(F(s+a0,y))) for s,v in e0)
        check(raw==alt,(x,y,'pairing'))
        if y==a0:check(raw==1,(x,'minimum'))
        check(1-ramp(F(a0,y))>=0,(x,y,'first'))
        n+=1
    print('rational least-bit pairing controls:',n)
def local():
    cnt=0
    for N in (12,30,84,100,180):
      for p in (2,3,5,7,11,13,17):
       for t in [F(0),F(2,7),F(1),F(5,4)]:
        a=b=F(0)
        for n in range(p*p):
         v=n*(N-n)
         if v%(p*p)==0:continue
         a+=(1-t if v%p==0 else 1)
         if v%p==0:b+=1
        want=(1-F(1,p) if N%p==0 else 1-2*t/p-2*(1-t)/(p*p))
        check(a/(p*p)==want,(N,p,t,'unmarked'))
        check(b/(p*p)==(0 if N%p==0 else F(2,p)-F(2,p*p)),(N,p,'marked'))
        cnt+=1
    print('squarefree and marked Euler controls:',cnt)
def flatness():
    # For rational C^2 smoothstep H(t)=1-10t^3+15t^4-6t^5 the third
    # derivative has zero mass and reconstructs H on [0,1] by hinge-square.
    h3=[-60,360,-360]
    check(sum(F(c,i+1) for i,c in enumerate(h3))==0,'zero leading residue')
    for j in range(41):
        t=F(j,40)
        integ=sum(c*((1-t**(i+3))/(i+3)-2*t*(1-t**(i+2))/(i+2)+t*t*(1-t**(i+1))/(i+1)) for i,c in enumerate(h3))
        check(-integ/2==1-10*t**3+15*t**4-6*t**5,t)
    print('exact zero-pole and hinge integral controls: 42')
def margins():
    for r in range(3,1001):
        eps=F(1,100*r*(1<<r))
        check(32*(1-r*(1<<r)*eps)>10,'dominance')
        check(F(r,100*(r+1))+F(1,3)<F(35,100),'sieve count')
    check(F(1,2)*(1+F(1,4))==F(5,8),'CRT spacing')
    b=Path(__file__).with_name('Proof.md').read_bytes()
    check(not any(i<32 and i!=10 for i in b),'source controls')
    check(b.count(b'$$')%2==0,'display pairing')
    print('exact rank margins and source integrity passed')
if __name__=='__main__':
    cases();local();flatness();margins()
