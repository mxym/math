"""Independent checks: no imports from the research packet; mpmath required."""
from itertools import combinations
import mpmath as mp
mp.mp.dps=65
d=3
w=mp.exp(2j*mp.pi/3)
bases=[mp.eye(3)]+[mp.matrix([[w**(a*r*r+b*r)/mp.sqrt(3) for b in range(3)] for r in range(3)]) for a in range(3)]
def outer(v): return v*v.H
def col(A,j): return A[:,j]
def ck(x): 
    if not x: raise AssertionError('independent check failed')
t=mp.mpf('1e-8')
D=mp.diag([1,mp.exp(1j*t),mp.exp(2j*t)])
res=[]
for i,j in combinations(range(3),2):
    for m in range(3):
        v=mp.matrix(3,1);v[i]=1/mp.sqrt(2);v[j]=-w**m/mp.sqrt(2)
        ws=[]
        for B in bases:
            vals=[abs((v.H*col(B,k))[0]) for k in range(3)]
            k=min(range(3),key=vals.__getitem__);ck(vals[k]<mp.mpf('1e-60'))
            ws.append(col(B,k))
        s=sum((outer(u) for u in ws[:3]),mp.matrix(3,3))+outer(D*ws[3])
        ck(abs(mp.det(s)-2*abs((v.H*D*ws[3])[0])**2)<mp.mpf('1e-60'))
        lam=mp.eighe(s,eigvals_only=True)[0];pred=mp.mpf((i-j)**2)/12
        ck(abs(lam/t**2-pred)<mp.mpf('1e-14'))
        res.append(float(pred/4))
print('Determinant identity and small eigenvalues checked at every Hesse ray:',sorted(res))
# Direct mixed Haar moments at independently chosen overlap. In general
# M(a,b;o)=E[p^a q^b]; compare its mixed derivative's affine-canceling second
# difference to the series in (V1) before factors 2*w_b*w_c.
def mom(a,b,o):
    if o==1: return mp.gamma(d)*mp.gamma(1+a+b)/mp.gamma(d+a+b)
    return (mp.gamma(d)*mp.gamma(1+a)*mp.gamma(1+b)/mp.gamma(d+a+b)
            *mp.hyp2f1(-a,-b,1,o))
def der(o):return mp.diff(lambda a,b: mom(a,b,o),(1,1),(1,1))
def s(o):
    if o==1: return mp.pi**2/3-3
    if o==0: return mp.mpf(0)
    return mp.nsum(lambda k:o**k/(k*(k-1))**2,[2, mp.inf])
def kernel(o):
    return s(o)/(d*(d+1))
# Rows of squared moduli for rotation in span(e1,e2), leaving e3 fixed.
o=mp.mpf(16)/25
over=[o,1-o,0,1-o,o,0,0,0,1]
xx=sum(der(v) for v in over)-9*der(mp.mpf(1)/3)
yy=sum(kernel(v) for v in over)-9*kernel(mp.mpf(1)/3)
ck(abs(xx-yy)<mp.mpf('1e-55'))
print('Unequal qutrit basis pair vs MUB: direct mixed Haar moment minus series:',mp.nstr(xx-yy,5),'gap',mp.nstr(xx,20))
