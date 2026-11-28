#!/usr/bin/env python3
"""Exact at-most-three test for nine-point pair orbits in five dimensions.\nUses NumPy for bounded signed integer arithmetic, not floating arithmetic.\n"""
import numpy as np
if not __debug__:raise RuntimeError("Run normal Python without -O.")
from math import isqrt
N=4;L=20;H=8;S=10000
from fractions import Fraction as F
def cosbound(j,n):
 if 2*j==n:return S//2
 x=F(2*355*j,3*113*n);v=term=F(1)
 for k in range(1,6):term=-term*x*x/((2*k)*(2*k-1));v+=term
 return (S*v).__floor__()
C=np.array([cosbound(i,L)for i in range(L//2+1)],np.int64)
st=np.array([(z,d,i,j)for z in range(H)for d in range(N)for i in range(L)for j in range(L)],dtype=np.int32)
z,d,px,py=st.T
def lroot(k):return np.array([isqrt(int(w)*S*S//(N*H*H))for w in k],dtype=np.int64)
xx=lroot(N*H*H+d*(H*H-(z+1)**2));yy=lroot(N*H*H+(N-d-1)*(H*H-(z+1)**2))
zl=z.astype(np.int64)*S//H;zh=((z.astype(np.int64)+1)*S+H-1)//H
def row(idx,lim=1,sign=1):
 u=np.abs(px-px[idx]);v=np.abs(py-py[idx])
 cu=C[np.minimum(L//2,np.minimum(u,L-u)+lim)];cv=C[np.minimum(L//2,np.minimum(v,L-v)+lim)]
 base=xx[idx]*xx*cu+yy[idx]*yy*cv
 return 2*(base+(zl[idx]*zl if sign>0 else -zh[idx]*zh)*S)<=3*S**3
def bits(v):return int.from_bytes(np.packbits(v,bitorder='little').tobytes(),'little')
def iterb(b):
 while b:
  t=b&-b;yield t.bit_length()-1;b^=t
n=len(st);print('vertices',n,flush=True)
same=[];opp=[]
for start in range(0,n,L*L):
 a=row(start,sign=1).reshape(H*N,L,L);b=row(start,sign=-1).reshape(H*N,L,L)
 for i in range(L):
  for j in range(L):
   same.append(bits(np.roll(a,(i,j),(1,2))));opp.append(bits(np.roll(b,(i,j),(1,2))))
ct=0;cc=0;keep=0;roots=[]
for idx in np.where((px==0)&(py==0)&(2*(d+1)>=N))[0]:
 A=bits(z>=z[idx]);B=bits((px<L//2)&(py<L//2))&A
 for sec in iterb(same[idx]&B):
  ct+=1;R=opp[idx]&opp[sec]&A
  if not R:continue
  cc+=1
  for third in iterb(R):
   ns=(same[third]&R&( -1<<third)).bit_count()
   if ns:
    keep+=ns
    roots.extend((idx,sec,third,i)for i in iterb(same[third]&R&(-1<<third)))
assert (ct,cc,keep)==(990,941,51160)
print('Coarse quadruples:',keep,flush=True)
D=128;P=320
assert D%N==D%H==P%L==0
sqrtlo=np.array([[isqrt((D**3+y*(D**2-x**2))*S*S//D**3)for y in range(D+1)]for x in range(D+1)],dtype=np.int64)
cs=np.array([cosbound(j,2*P)for j in range(P+1)],dtype=np.int64)
sig=((0,1,1),(0,2,-1),(0,3,-1),(1,2,-1),(1,3,-1),(2,3,1))
width=np.tile([D//H,D//N,P//L,P//L],(4,1));width[0,2:]=0
rows=st[np.array(roots,dtype=int)].reshape(-1,4,4)*np.array([D//H,D//N,P//L,P//L])
def narrow(rows,width):
 if not len(rows):return rows
 z=rows[:,:,0];v=rows[:,:,1];a=sqrtlo[z+width[:,0],v];b=sqrtlo[z+width[:,0],D-v-width[:,1]]
 lo=z.astype(np.int64)*S//D;hi=((z+width[:,0]).astype(np.int64)*S+D-1)//D
 ok=(2*(v[:,0]+width[0,1])>=D)&np.all(z[:,0,None]<=z[:,1:]+width[None,1:,0],axis=1)
 cent=2*rows[:,:,2:]+width[None,:,2:]
 for i,j,t in sig:
  u=np.abs(cent[:,i]-cent[:,j]);d=np.minimum(P,np.minimum(u,2*P-u)+width[i,2:]+width[j,2:])
  aa=a[:,i]*a[:,j]*cs[d[:,0]];bb=b[:,i]*b[:,j]*cs[d[:,1]];zz=(lo[:,i]*lo[:,j]if t>0 else -hi[:,i]*hi[:,j])*S
  ok&=2*(aa+bb+zz)<=3*S**3
 return rows[ok]
rows=narrow(rows,width);levels=[len(rows)]
# The three fixed subdivisions suffice; in every case test both children.
for i,j in [(2,0),(2,1),(3,1)]:
 assert width[i,j]%2==0
 width[i,j]//=2;out=[]
 for a0 in range(0,len(rows),30000):
  v=rows[a0:a0+30000];u=v.copy();u[:,i,j]+=width[i,j];out.extend((narrow(v,width),narrow(u,width)))
 rows=np.concatenate(out);levels.append(len(rows))
assert levels==[14065,1845,39,0]
print('After exact anchor and coordinate subdivisions:',levels)
# Analytic arithmetic: (1+sqrt2)/2 + 1/3 > 3/2 iff sqrt2>4/3.
assert 18>16
