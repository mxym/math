"""Exact characteristic polynomials in the 120-scaled coordinates; no author imports."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
def check(p,msg):
    if not p: raise ArithmeticError(msg)
# Off-diagonal unit is sqrt(3); inputs explicit, not produced by an angle loop.
c=(3,3,-2,-2,-2)
B=((12,12,0,96),(8,8,0,104),(12,8,0,100),(9,11,1,100),(9,11,-1,100))
U=Counter();V=Counter();spectra=[]
for i,j in product(range(5),repeat=2):
    a,d,b,f=[Q(s+t,2) for s,t in zip(B[i],B[j])]
    tr=a+d;det=a*d-3*b*b
    check(a>0 and det>0 and f>0 and tr+f==120,'not faithful')
    roots=[z for z in range(8,13) if z*z-tr*z+det==0]
    if len(roots)==1:roots*=2
    check(len(roots)==2 and sum(roots)==tr and roots[0]*roots[1]==det,'wrong roots')
    for z in roots:U[z]+=c[i]*c[j]
    V[f]+=c[i]*c[j]
    spectra.append((sorted(roots+[f]),c[i]*c[j]))
check(U=={8:-6,9:24,10:-36,11:24,12:-6},'upper distribution')
check(V=={96:9,98:-36,100:54,102:-36,104:9},'flag distribution')
check(sum(c)==0 and sum(c[i]*c[j] for i,j in product(range(5),repeat=2))==0,'not a contrast')
# Moments 0,1,2,3 vanish globally; the two fourth-order differences have the stated scale.
for w,step,fac in ((U,1,-6),(V,2,9)):
    check([sum(n*k**r for k,n in w.items()) for r in range(5)]==[0,0,0,0,24*step**4*fac],'moment')
check(Q(96,12)**2>Q(9,6)*2**4,'all-order ratio')
# Zhang's published case: τ-normalization factor 1/3 removed; one fixed contrast cannot cover q=2.
Z=((2,1,1),(9,1,2),(2,7,1),(8,8,5),(8,9,8));d=(-10,10,10,-20,10)
delta=[Q(sum(k*z[i] for k,z in zip(d,Z)),40) for i in range(3)]
delta += [-delta[0]-delta[1]]
check(delta==[Q(1,4),0,0,-Q(1,4)],'Zhang weighted matrices')
check(-Q(1,2)*(delta[0]**2+delta[1]**2+2*delta[2]**2+delta[3]**2)==-Q(1,16),'Zhang q=2')
if __name__=='__main__': print('PASS: 25 polynomial spectral factorizations; exact quartic stencils and no rounding; Zhang q=2 contrast = -1/16')
