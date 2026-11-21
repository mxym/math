"""Exact positive controls. The five-label classification in the note is analytic."""
from fractions import Fraction
from math import gcd, prod
def ck(test, info):
    if not test:raise ValueError(info)

N=128
p=[3,5,7,11,13,23,29,41]
rows=[]
for i,q in enumerate(p):
    n=N-q;row=[]
    for r in p:
        a=0
        while n%r==0:a+=1;n//=r
        row.append(a)
    ck(n==1 and row[i]==0 and sum(row)>=2,('actual complementary row',q))
    rows.append(row)
B=[[int(i==j)-rows[i][j] for j in range(8)] for i in range(8)]
v=[3,1,-22,-11,-17,-18,-5,-2]
c=[1,1,-1,-1,-1,-1,1,1]
sign=[-1,1,-1,-1,1,-1,1,1]
ck(all(sum(b*t for b,t in zip(row,v))==0 for row in B),'right kernel')
ck(all(sum(c[i]*B[i][j] for i in range(8))==0 for j in range(8)),'left')
ck(all(prod(s if b%2 else 1 for b,s in zip(row,sign))==-1 for row in B),'signed torus')
# Every torus point at t=x_5 is found without root extraction. Resolve the
# eight row equations in the order shown, with each newly solved exponent ±1.
solved={1}
for i,j in [(0,0),(1,7),(7,6),(6,3),(2,2),(3,4),(4,5)]:
    ck(j not in solved and abs(B[i][j])==1 and {l for l in range(8) if l!=j and B[i][l]}<=solved,'full-coverage monomial step')
    solved.add(j)
ck(len(solved)==8 and len(set(v))==8,'one-dimensional exact chart')
ck(all((s*pow(5,e,N)-q)%N==0 for s,e,q in zip(sign,v,p)),'actual 128 point')
g=sum(Fraction(ci,pi) for ci,pi in zip(c,p))
ck(g.numerator%N==0 and gcd(g.denominator,N)==1,'true derivative')
# t^3*g=sum c_i*sign_i*t^(3-v_i). No collisions occur here.
poly={3-a:b*s for a,b,s in zip(v,c,sign)}
ck(poly=={0:-1,2:1,25:1,14:1,20:-1,21:1,8:1,5:1},'actual eliminating polynomial')
value=sum(c*5**e for e,c in poly.items())
ck(value and value%N==0,'integer divisibility, including 2-power multiplicity')
print('128 exact torus and derivative: F(5)=',value,'divisible by 128')
# Local reciprocal examples are not claims of additional EACs.
N,x,y,h=94,3,13,2
ck(N==x+y+h*x*y and y*y>N and (x*h)**2<N,'large upper test')
a,b=3,5
ck(pow(x,a,N)*pow(y,b,N)%N in (1,N-1),'two-label congruence fixture')
W=x**(2*(a+b))-(1+h*x)**(2*b)
ck(W and W%N==0,'eliminated y')
N,x,y,h=1132,5,7,32
ck(N==x+y+h*x*y and (N-x)%(y*y)==(N-y)%(x*x)==0 and (x*y)**2>N,'squared pair fixture')
d,rem=divmod(h*(x+y)+1,x*y)
ck(not rem and d==11 and x*d<=2*h+1 and (d*x*x+1)%(x+y)==0,'divisor recovery')
print('large upper and mutually squared large-product local fixtures: PASS')
