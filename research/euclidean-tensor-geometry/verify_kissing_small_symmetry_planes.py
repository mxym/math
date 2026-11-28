#!/usr/bin/env python3
"""Exact two-variable checking of the triangle supports for a reflected heptad."""
from math import comb
from fractions import Fraction as F
GO=[[1,289940,-184430,209100],[1,473841,-317170,301310],[1,101010,-41630,92430],[1,169910,-95990,143020],[1,528580,-352740,346620],[1,69760,-11960,53200],[1,575210,-388820,346810],[1,319780,-205530,228000],[1,506351,-339330,324690],[1,214580,-129410,169250],[1,131350,-66380,117460],[1,83290,-25650,72600],[1,506341,-340230,316200],[2,-67260,72470,82540],[2,283220,-92650,288150],[2,-178630,127150,22850],[2,973520,-388850,385410],[2,455361,-170140,399950],[2,112060,-13170,184260],[2,412240,-132650,161450],[2,22510,29290,132530],[2,215220,-61340,246080],[2,368250,-131270,342340],[2,270670,-66170,99050],[2,619650,-228410,248480],[2,139450,-2530,36290]]
D=100000
def trim(A):
 return {k:v for k,v in A.items()if v}
def plus(*ps):
 A={}
 for p in ps:
  for k,x in p.items():A[k]=A.get(k,0)+x
 return trim(A)
def times(a,b):
 A={}
 for (i,j),c in a.items():
  for (k,l),d in b.items():A[i+k,j+l]=A.get((i+k,j+l),0)+c*d
 return trim(A)
def sc(a,p):return {k:a*v for k,v in p.items()}
def powp(p,n):
 q={(0,0):1}
 for _ in range(n):q=times(q,p)
 return q
one={(0,0):1};x={(1,0):1};y={(0,1):1}
def axis(t):
 tt=times(t,t);d=plus(one,tt);n=plus(one,sc(-1,tt))
 h=plus(sc(4,powp(n,4)),sc(-1,times(powp(n,2),powp(d,2))))
 return d,n,h
dx,nx,fx=axis(x);dy,ny,fy=axis(y);den=times(powp(dx,4),powp(dy,4))
u=times(powp(dx,3),powp(dy,3));cn=plus(times(nx,ny),sc(-4,times(x,y)))
adm=plus(sc(3,powp(plus(x,y),2)),sc(-1,powp(plus(one,sc(-1,times(x,y))),2)))
def poly(R,a,b,c):
 return plus(sc(4*a,den),sc(4*b*R,times(times(nx,dy),u)),sc(4*b,times(times(ny,dx),u)),sc(4*c,times(cn,u)),sc(-R*D,times(fx,powp(dy,4))),sc(-D,times(fy,powp(dx,4))))
def bern(p,d=8):
 # [0,577351/1000000]^2 strictly contains the parameter rectangle.
 L=F(577351,1000000);t=[[sum(F(cc)*L**(i+j)*comb(u,i)*comb(v,j)/(comb(d,i)*comb(d,j))for (i,j),cc in p.items()if i<=u and j<=v) for v in range(d+1)]for u in range(d+1)]
 from math import lcm
 h=lcm(*(v.denominator for row in t for v in row))
 return [[v.numerator*(h//v.denominator)for v in row]for row in t]
def trans(a):return list(zip(*a))
def cut(a,dim):
 if dim:a=trans(a)
 n=len(a)-1;left=[];right=[]
 for row in a:
  z=list(row);lo=[];hi=[]
  for j in range(n+1):
   lo.append(z[0]<<(n-j));hi.append(z[-1]<<(n-j));z=[p+q for p,q in zip(z,z[1:])]
  left.append(lo);right.append(list(reversed(hi)))
 return (trans(left),trans(right)) if dim else (left,right)
def check(q,a,dep=0):
 if min(map(min,q))>=0 or max(map(max,a))<0:return 1
 if dep>62:raise ArithmeticError("unresolved triangle plane")
 l,r=cut(q,dep%2);ll,rr=cut(a,dep%2)
 return 1+check(l,ll,dep+1)+check(r,rr,dep+1)
if __name__=='__main__':
 assert 3*577351**2>10**12
 B=bern(adm)
 n=[check(bern(poly(*row)),B) for row in GO]
 print("PASS all",len(GO),"rational triangle planes; Bernstein cells",sum(n),"maximum",max(n),n)
