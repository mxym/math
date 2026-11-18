"""Independent exact certificate: polynomial convolutions; negative-log series on [1/2,1]."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from functools import lru_cache
import math
def ck(v,msg):
    if not v:raise ValueError(msg)
def conv(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return r
def move(p,num,den,n):
    # coefficients of den^n p(num/den), via Horner.
    P=[p[n]]; D=[1]
    for i in reversed(range(n)):
        P=conv(P,num);D=conv(D,den);P+=[0]*(len(D)-len(P))
        for j,y in enumerate(D):P[j]+=p[i]*y
    return P
def check_poly():
    S=[p for p in product(range(3),repeat=4) if p[0]+p[1]==p[2]+p[3]]
    W=Counter((p.count(0),p.count(2)) for p in S) # center set to 1
    ck(W=={(4,0):1,(0,0):1,(0,4):1,(2,0):4,(0,2):4,(2,2):4,(1,1):4},W)
    # target v^(q−1) W_x < W_y at endpoints v=y/x; x=1 yields powers in u=v^1/7.
    p=[0]*22
    for (i,j),coef in W.items():
        if j:p[7*(j-1)]+=coef*j
        if i:p[7*j+3]-=coef*i
    ck(all(k%4==0 for k in p),'derivative 4')
    p=[k//4 for k in p]
    got=move(p,[0,1],[1,1],21)
    wanted=[1,21,210,1327,5931,19890,51816,107104,177842,238602,258699,225435,156023,84063,34206,10122,2191,477,165,48,4,0]
    ck(got==wanted and min(got[:-1])>0,got)
    # x→0: only total degree 2 survives; as w=v^1/3, factor 4(1-w)^3(1+w).
    p=[0]*5
    for (i,j),coef in W.items():
        if i+j!=2:continue
        if j:p[3*(j-1)]+=coef*j
        if i:p[3*j+1]-=coef*i
    ck(p==conv(conv(conv([4,-4],[1,-1]),[1,-1]),[1,1]),p)
    print('Re-derived quartic, both normalized derivative coefficients, all 22 transformed coefficients.')
def scaled(a,x):return (a*x[0],a*x[1]) if a>=0 else (a*x[1],a*x[0])
def add(x,y):return x[0]+y[0],x[1]+y[1]
def neglog(v):
    # v in [1/2,1], -log(v)=sum_{i>=1}(1-v)^i/i, elementary geometric tail.
    ck(F(1,2)<=v<=1,v)
    r=1-v; term=r; val=F(0);J=128
    for i in range(1,J+1):
        val+=term/i;term*=r
    return val,val+term/((1-r)*(J+1))
@lru_cache(maxsize=None)
def log(x):
    x=F(x);k=0
    ck(x>0,'positive')
    while x>1:x/=2;k+=1
    while x<F(1,2):x*=2;k-=1
    return add(scaled(-1,neglog(x)),scaled(k,neglog(F(1,2))))
def h(q,z):
    return add(log(3*(1+z)/(1+6*z)),scaled(1-q/2,log(z)))
def P(z):return 1+12*z+6*z*z
def inunit(x):
    s=10**25
    return math.floor(x[0]*s),math.ceil(x[1]*s)
def ends():
    qs=[F('1.4702039297178894'),F('1.4702039297178896')]
    Ls=[F('0.32606289730212337828'),F('0.32606289730212362033')]
    wanted=[(-2806923826,-2805386773),(2716006432,2717543485)]
    ck(h(qs[0],F(1,4))[0]>0,'bracketing shoulder')
    for k,(q,lo) in enumerate(zip(qs,Ls)):
        hi=lo+F(1,10**20)
        ck(F(1,4)<lo<hi<1 and h(q,lo)[0]>0 and h(q,hi)[1]<0,'bracket')
        a=log(1+6*lo)[0],log(1+6*hi)[1]
        b=log(P(lo))[0],log(P(hi))[1]
        c=add(scaled(4,a),scaled(q-4,b))
        ck((k==0 and c[1]<0) or (k==1 and c[0]>0),'sign')
        ck(inunit(c)==wanted[k],('round',inunit(c),wanted[k]))
        print('qlogM scaled by 1e25:',inunit(c),'logh ends:',inunit(h(q,lo)),inunit(h(q,hi)))
    ck(F('2.7207109973971711')<4/qs[1]<4/qs[0]<F('2.7207109973971716'),'reciprocals')
    print('Both root brackets, signs, published endpoint enclosures and exponent reciprocal passed.')
if __name__=='__main__':check_poly();ends()
