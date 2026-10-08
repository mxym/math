#!/usr/bin/env python3
"""Standalone exact verifier, Python standard library only.
Run next to counterexample_vectors_n200.csv. No optimizer, float, numerical
integration, or stored polynomial norm is trusted or used.
"""
from pathlib import Path
import csv, math, hashlib
ROOT=Path(__file__).resolve().parent
PATH=ROOT/'counterexample_vectors_n200.csv'
with PATH.open() as file:
 rows=list(csv.DictReader(file))
V=[((int(r['a_real']),int(r['a_imag'])),(int(r['b_real']),int(r['b_imag']))) for r in rows]
n=len(V); assert n==200
assert max(abs(t) for v in V for z in v for t in z)<=20
assert min(sum(t*t for z in v for t in z) for v in V)>0
N=n*(n-1)//2

def plus(z,w):return (z[0]+w[0],z[1]+w[1])
def times(z,w):return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def scale(z,k):return (z[0]*k,z[1]*k)
def square_abs(z):return z[0]**2+z[1]**2

def multiply_linear(P,a,b):
 out=[(0,0)]*(len(P)+1)
 for k,c in enumerate(P):
  out[k]=plus(out[k],times(a,c));out[k+1]=plus(out[k+1],times(b,c))
 return out

F=[(1,0)];S=[]
for j,(a,b) in enumerate(V,1):
 old=F
 F=multiply_linear(old,a,b)
 if j==1:continue
 S=multiply_linear(S,a,b) if S else [(0,0)]*(j-1)
 for k in range(j-1):
  S[k]=plus(S[k],plus(scale(times(b,old[k]),j-1-k),scale(times(a,old[k+1]),-(k+1))))
assert len(F)==n+1 and len(S)==n-1
P=sum(math.factorial(n-k)*math.factorial(k)*square_abs(c) for k,c in enumerate(F))
H=sum(math.factorial(n-2-k)*math.factorial(k)*square_abs(c) for k,c in enumerate(S))
D=H-N*P
assert P>0 and D>0
assert 23*N*P < 1000*D < 24*N*P
assert D%2==0
print('PASS: exact integer arithmetic gives 23/1000 < (H - N P)/(N P) < 24/1000.')
print('Thus P_q derivative at q=1 for A=V V* is -D/2 < 0.')
print('n =',n,'; positive D has',len(str(D)),'decimal digits.')
print('CSV SHA256 =',hashlib.sha256(PATH.read_bytes()).hexdigest())
print('Full exact D =',D)
