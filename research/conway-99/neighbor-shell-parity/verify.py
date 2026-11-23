"""Reproduce the rank-42/neighbor order-four torus transfer and exact Fourier-block check. Requires SymPy only."""

from itertools import combinations_with_replacement, product
from math import factorial, isqrt
from fractions import Fraction as Q
from collections import Counter
from functools import cache
import sympy as S
J=34
def one(r):
 z=[0]*(J+1);mom=z.copy()
 lim=isqrt((2*J+r*r)//7)
 for m in combinations_with_replacement(range(-lim,lim+1),7):
  if sum(m)!=r:continue
  n=(7*sum(x*x for x in m)-r*r)//2
  if n>J:continue
  w=factorial(7)
  for v in Counter(m).values():w//=factorial(v)
  z[n]+=w;mom[n]+=w*sum((7*x-r)**3 for x in m)
 return z,mom
def conv(a,b):
 return [sum(a[i]*b[j-i] for i in range(j+1)) for j in range(J+1)]
def powser(a,k):
 if not k:return [1]+[0]*J
 return conv(a,powser(a,k-1))
def eisen(k):
 t=[1]+[0]*J
 for j in range(7,J+1,7):t[j]=({2:-24,4:240,6:-504}[k])*sum(i**(k-1) for i in range(1,j//7+1) if j//7%i==0)
 return t
e2,e4,e6=map(eisen,[2,4,6])
V=[one(r) for r in range(7)];g=(2,2)
def mul(a,b):return ((a[0]*b[0]-a[1]*b[1])%7,(a[0]*b[1]+a[1]*b[0])%7)
def qq(a):return 3*(a[0]**2+a[1]**2)%7
HL=[(1,0)]
for i in range(7):HL.append(mul(HL[-1],g))
keys=[(j,a) for j in range(J+1) for a in product(range(7),repeat=2) if qq(a)==j%7 and a<((-a[0])%7,(-a[1])%7)]

cands=[]
for k in range(2):
 F0={a:[sum((2*i-j)*V[b[0]][0][i]*V[b[1]][0][j-i] for i in range(j+1)) for j in range(J+1)] for a in product(range(7),repeat=2) for b in [mul(a,HL[k])]}
 for h in range(8):
  for m in range(3):
   for n in range(4):
    if h+3*m+2*n!=7:continue
    ef=conv(powser(e4,n),powser(e6,m));R={al:conv(ef,f) for al,f in F0.items()};cands.append([R[al][j] for j,al in keys])
  w=8+2*h;F0={a:[Q(j,7)*v-Q(w,12)*ww for j,(v,ww) in enumerate(zip(f,conv(e2,f)))] for a,f in F0.items()}
C=S.Matrix(cands).T;_,p=C.to_DM().rref();C=C[:,list(p)]
for start in (8,):
 I=[i for i,(j,a) in enumerate(keys) if j<start];ns=C[I,:].nullspace();D=C*S.Matrix.hstack(*ns);I0=[i for i,(j,a) in enumerate(keys) if start<=j<=11]
 _,row=D[I0,:].T.rref();I1=[I0[r] for r in row];print('start',start,'span',len(I1),'expected',2*(12-start))
 assert len(I1)==2*(12-start), 'test forms do not span the required seed data'
 if len(I1)==2*(12-start):
  W=D*D[I1,:].inv();print('seeds',[keys[i] for i in I1]);print('j12',[(k,list(W[i,:])) for i,k in enumerate(keys) if k[0]==12])

  expected=[[-1,-1,1,1,-1,0,1,1],[1,1,-1,-1,1,0,-1,-1],[1,-1,-1,1,0,-1,1,-1],[-1,1,1,-1,0,1,-1,1]]; assert [list(W[i,:]) for i,k in enumerate(keys) if k[0]==12]==expected
  checks={8:'1000',9:'0100',10:'0010',11:'0001',12:'0010',13:'0000',15:'0001',16:'1000',17:'0000',18:'0000',19:'0000',20:'0010',22:'0000',23:'0001',24:'0000',25:'0100',26:'0010',27:'0000',29:'0000',30:'0000',31:'0000',32:'1000',33:'0000',34:'0000'}
  for t in range(8,J+1):
   if t%7==0:continue
   sl=[i for i,(j,a) in enumerate(keys) if j==t];used=set();sel=[]
   for i in sl:
    a=keys[i][1];b=mul((0,1),a);b=min(b,((-b[0])%7,(-b[1])%7)); 
    if a not in used:sel.append(i);used.update([a,b])
   parity_row=list(W[sel[0],:]+W[sel[1],:])
   assert all(z.is_Integer for z in parity_row), 'non-integral parity coefficient'
   pix=[int(z)%2 for z in parity_row]
   assert len(sel)==2 and all(pix[2*k]==pix[2*k+1] for k in range(4))
   mask=''.join(map(str,pix[::2]));assert mask==checks[t];print(t,mask)

def verify_fourier_order4():
 rr=[next(z for z in product(range(7),repeat=2) if qq(z)==a) for a in range(1,7)]
 for x in rr:
  for y in rr:
   v=[[0,0] for r in range(7)]
   for l,h in enumerate(HL):
    z=mul(h,y);r=(x[0]*z[0]+x[1]*z[1])%7;v[r][l%2]+=1 if l%4 in (0,1) else -1
   assert any(w!=v[0] for w in v[1:])
 print('All 36 order-four Fourier coefficients nonzero, by cyclotomic independence over Q(i).')
verify_fourier_order4()

def verify_five_point_odd_kernel():
    def q(v):
        a,b,c,d=v
        return (a*b+c*c+d*d)%7
    def polar(v,w):
        a,b,c,d=v; e,f,g,h=w
        return (a*f+b*e+2*c*g+2*d*h)%7
    def normalize(v):
        scale=pow(next(n for n in v if n),-1,7)
        return tuple(n*scale%7 for n in v)
    points={normalize(v) for v in product(range(7),repeat=4) if any(v) and q(v)==0}
    witness=((1,5,2,6),(1,6,4,5),(0,0,1,2),(0,0,1,3),(1,3,1,3))
    assert len(points)==50 and len({normalize(v) for v in witness})==5
    assert all(q(v) in (3,5,6) for v in witness)
    assert all(sum(polar(v,w)==0 for w in witness)%2==0 for v in points)
    print("Verified the odd five-point kernel on all 50 isotropic lines.")

verify_five_point_odd_kernel()
