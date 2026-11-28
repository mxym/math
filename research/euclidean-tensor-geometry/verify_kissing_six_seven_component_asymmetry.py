#!/usr/bin/env python3
"""Exact anisotropic component inequality; no external libraries or optimization."""
from fractions import Fraction as F
import itertools,sys,math
def require(x,msg):
 if not x:raise ValueError(msg)
# One certified rational circulant lower bound for quartic deficiency on the cube.
D=10**6;row=[-597788,-398531,93327,479339];H=[[F(row[min((i-j)%7,(j-i)%7)],D)for j in range(7)]for i in range(7)]
def ldl(A):
 if not A:return []
 p=A[0][0];require(p>0,'nonpositive pivot')
 a=[r[0]for r in A[1:]];return [(p,a)]+ldl([[A[i+1][j+1]-x*y/p for j,y in enumerate(a)]for i,x in enumerate(a)])
def quadratic_inv(A,y):
 ans=0
 for p,col in ldl(A):
  z=y[0];ans+=z*z/p;y=[b-z*c/p for b,c in zip(y[1:],col)]
 return ans
def verify_cube():
 require((1-H[0][0])/6<=F(3,10),'second derivative cutoff')
 for e in itertools.product((-1,0,1),repeat=7):
  S=[i for i in range(7)if not e[i]];B=[i for i in range(7)if e[i]]
  A=[[F(7,10)*(i==j)-H[i][j] for j in S]for i in S];u=[sum(H[i][j]*e[j]for j in B)for i in S]
  require(sum(e[i]*e[j]*H[i][j]for i in B for j in B)+quadratic_inv(A,u)<=0,'failed ternary face '+str(e))
 print('PASS 2187 exact Schur faces',flush=True)
verify_cube()
# The cyclically averaged Gram matrix can have rank seven. Cover its full spectral simplex.
def I(l,h=None):return (F(l),F(l)if h is None else F(h))
def add(x,y):return(x[0]+y[0],x[1]+y[1])
def neg(x):return(-x[1],-x[0])
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 z=[a*b for a in x for b in y];return min(z),max(z)
def sc(x,y):return mul(x,I(y))
def sq(x):return(I(0)[0]if x[0]<=0<=x[1] else min(x[0]**2,x[1]**2),max(x[0]**2,x[1]**2))
def sm(xs):
 z=I(0)
 for v in xs:z=add(z,v)
 return z
t=I(F(1246979603717,10**12),F(1246979603718,10**12))
pt=lambda t:t**3+t*t-2*t-1
require(pt(t[0])<0<pt(t[1])and t[0]>1,'isolate the root 2 cos(2pi/7)')
ct=[I(1),sc(t,F(1,2)),sc(sub(sq(t),I(2)),F(1,2)),sc(sub(sub(I(1),t),sq(t)),F(1,2))]
ct=ct+ct[1:][::-1]
require(len(ct)==7,'seven cosine residues')
eig=[sm([I(row[0],row[0])]+[sc(ct[(j*k)%7],2*row[j])for j in range(1,4)])for k in range(4)]
eig=[sc(x,F(1,D))for x in eig];require(min(x[0]for x in eig)>F(-21,10)and max(x[1]for x in eig)<F(3,100),'circulant norm and top eigenvalue')
w=F(4975124,10**6);W=F(47868660,10**6);c=F(7,20);one=I(1)
def phi(a,ee):
 gamma=sm([mul(x,z)for x,z in zip(eig,a)])
 lc=sm([sc(mul(x,sq(z)),F(1,n))for x,z,n in zip(eig,a,[1,2,2,2])])
 ls=sub(sm([sc(sq(mul(x,z)),F(1,n))for x,z,n in zip(eig,a,[1,2,2,2])]),sc(sq(gamma),F(1,6)))
 return W*W/48-W+w*w*(1/w-ee)+w*W*gamma[0]/12-w*w*lc[1]/2-w*w*ls[1]/(16*c)
def fup(z):
 f=lambda x:x**4-x*x/4
 return max(f(z[0]),f(z[1]),F(0)if z[0]<=0<=z[1]else F(-1))
tol=F(1,300)
count=0;maxd=0
def go(box,d):
 global count,maxd
 count+=1;maxd=max(maxd,d);rem=sub(one,sm(box));rem=(max(0,rem[0]),min(1,rem[1]))
 if rem[0]>rem[1]:return
 a=list(box)+[rem]
 dots=[sm([mul(a[i],ct[(i*k)%7])for i in range(4)])for k in (1,2,3)]
 if dots[0][0]>=F(-1,2) or any(l>F(1,2)for l,h in dots):return
 dots=[(max(F(-1),l),min(F(-1,2)if k==0 else F(1,2),h))for k,(l,h)in enumerate(dots)]
 # Explicitly discard intervals incompatible with normalized products.
 if any(l>h for l,h in dots):return
 ee=(F(3,4)+2*sum(fup(z)for z in dots))/7
 if W*W/48-W+w*w*(1/w-ee)>tol or phi(a,ee)>tol:return
 require(d<=100 and count<7000000,'unresolved 3-simplex '+str((box,ee)))
 j=d%3;l,h=box[j];m=(l+h)/2
 for z in ((l,m),(m,h)):
  b=box.copy();b[j]=z;go(b,d+1)
go([I(0,1)]*3,0);print('PASS all cyclic Gram averages of any rank:',count,maxd,'margin',tol,flush=True)

# The ten lists and the component-level charges of the pinned predecessor;
# only the eight containing a seven-component are used.
weights={1:1333333,7:4975124,9:6211180,11:7329707,13:8527648,25:15468315,27:16540366,29:17692255,31:18892824,33:20064010}
lists=[(7,7,27,33),(7,7,29,31),(7,9,27,31),(7,9,29,29),(7,11,25,31),(7,11,27,29),(7,13,25,29),(7,13,27,27)]
require(min(F(weights[1]+sum(weights[v]for v in r),10**6)for r in lists)==W,'template charge floor')
require(W/24-1-w*F(21,10)/12>0,'monotonicity in total charge')
require(W**2/48-W+w**2*(1/w-F(3,28))>tol,'case no strict averaged lag')
err=w*w*(F(23,4)+F(3,200)+F(21,10)**2/(16*c))
require(err<163 and F(163,225**2)<tol,'perturbation budget')
print('PASS RMS separation > 1/225 in all eight eligible size lists.') 
