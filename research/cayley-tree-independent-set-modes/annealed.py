"""Optional certificate refining interval.py. No floating point or random sampling."""
from fractions import Fraction as F
import interval as I
I.K=600
a,A,s,S=I.atom(0),I.atom(I.K),I.atom(0),I.atom(I.K)
for _ in range(13):
    a,A=I.ordinary(A,True),I.ordinary(a,False)
    s,S=I.divide(a,S,True),I.divide(A,s,False)
lo,hi=I.q(s),I.q(S)
if not F(305300,10**6)<=lo<=hi<=F(306955,10**6):raise ValueError('root bracket')
x=F(3074,10000)
y=(1-x)**2/x
w=(y-1)/(y+1)
proof=2*(w+w**3/3+w**5/5)-x/(1-x)
if not 0<w<1 or proof<=0:raise ValueError('annealed derivative comparison')
print("quenched outward (units 10^-6):", lo*10**6//1,-((-hi*10**6)//1))
print("annealed derivative lower bound at 0.3074:",proof)
