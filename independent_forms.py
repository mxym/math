from fractions import Fraction as F
from functools import lru_cache

@lru_cache(None)
def logs(t):
    n=180
    h=sum(t**j/j for j in range(1,n+1))
    return h,h+t**(n+1)/((n+1)*(1-t))
lo2,hi2=logs(F(1,2)); lo54,hi54=logs(F(1,5))
lo5,hi5=lo2*2+lo54,hi2*2+hi54
def level(P,K):
    p=P-2*K
    assert p>0 and K>0
    return p*lo2-K*hi54,p*hi2-K*lo54
p,k=138463487,59632978
q,l=241187130,103873643
L=F(21,3*(1<<29)); Kcap=1300000000
h=-level(q,l)[0]; g=level(p,k)[1]
# Set coordinates independently from the interval projection, then exact gap test.
v_max=(h*Kcap+l*L)//lo2
w_min=(-k*L)//lo2 # floor of the lower bound, one extra conservative cell
w_max=g*Kcap//lo2
assert (v_max,w_min,w_max)==(4,-2,11)
rho=F(2321929,1_000_000)
assert hi5<rho*lo2
S=[sum(rho**j for j in range(i)) for i in range(22)]
a=F(3,4)
candidates=[]
suspects=[]
def limit(H,r):
    return 21*a+(H-a)*(S[22-r]+r-1)
for v in range(1,v_max+1):
    for w in range(w_min,w_max+1):
        P=p*v+q*w;K=k*v+l*w
        if K<=0 or K>=Kcap:continue
        lo,hi=level(P,K)
        if hi<=0 or lo>=L:continue
        assert 0<lo<hi<L
        r=sum(lo>(i-1)*F(1,3*(1<<29))+(22-i)*F(1,(1<<40)-1) for i in range(1,22))
        assert r>=1
        candidates.append((P,K,v,w,r))
        if K<=limit(40,r): suspects.append((P,K,v,w,r))
assert len(candidates)==22 and suspects==[(1103212007,475127550,1,4,2)]
P,K,_,_,_=suspects[0]
z=F(17,10)*(1<<30)
assert level(P,K)[0]>1/(z-1)+F(1,3*(1<<29))+F(19,(1<<60)-1)
assert K>limit(60,3) and K>limit(F(154,5),2)
print('Independent log-series and coordinate census:',len(candidates),suspects)
print('Q19 lambda and strict rational margins (formatted approximately):',float(level(P,K)[0]),float(K-limit(60,3)),float(K-limit(F(154,5),2)))
