"""Finite consistency tests only. The asymptotic existence theorem is analytic."""
from itertools import product, combinations
from math import comb
def graph(m,l,L,edges):
 h=m*l; n=h+L; N=[0]*n
 def edge(v,w):N[v]|=1<<w;N[w]|=1<<v
 for i in range(m):
  for a,b in combinations(range(i*l,(i+1)*l),2):edge(a,b)
 for j in range(h*L):
  if edges>>j&1:edge(j//L,h+j%L)
 return N
def independent_maximal(J,N):
 n=len(N); covered=J
 for v in range(n):
  if J>>v&1:
   if J&N[v]:return False
   covered|=N[v]
 return covered==(1<<n)-1
def candidates(m,l,L,N):
 h=m*l;A=((1<<L)-1)<<h
 for picks in product(range(-1,l),repeat=m):
  S=0; hit=0
  for i,v in enumerate(picks):
   if v>=0:
    S|=1<<(i*l+v);hit|=N[i*l+v]
  yield S | (A&~hit),-1 not in picks
totals=[0,0,0]
for mask in range(1<<8):
 m=l=L=2;n=m*l+L;N=graph(m,l,L,mask)
 bs={j for j in range(1<<n) if independent_maximal(j,N)}
 ps,full=zip(*candidates(m,l,L,N))
 assert bs=={j for j in ps if independent_maximal(j,N)}
 assert all(j in bs for j,b in zip(ps,full) if b)
 for T in range(1<<n):
  if any(not(j&T) for j,b in zip(ps,full) if b):assert any(not(j&T) for j in bs)
 totals[0]+=1;totals[1]+=sum(full);totals[2]+=1<<n
# Binomial combinatorial inequality used for property 2, checked rationally.
for r in range(1,151):
 for k in range(1,r+1):assert comb(r,k)*k**k>=r**k
print('PASS:',totals[0],'graphs;',totals[1],'full-representative completions;',totals[2],'mixed test sets; exact integer binomial checks r<=150')
