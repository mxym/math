"""Integer 13-dimensional frame and 2-dimensional determinant certificate.
No floating point, solver, or external data required. See cost21-final-plane.md.
"""
from itertools import combinations_with_replacement as cwr
from math import isqrt
def fibers(n,L):
 out={}
 for i in range(18*L):
  vals=[]
  for e in range(n*(n-1)//2+1):
   T=3*n*(n-1)-2*e
   V=13*(9*(n-1)*n*n+(n-6)*2*e*n-4*e*e)-T*T
   if V<0 or n*n*i>L*((21-3*n)*n+14*e):continue
   def J(y):
    return n*(13*(n-1)*(3*L+y)**2-(n-13)*(18*L-y)**2)+182*e*L*(L-2*y)
   if max(J(i),J(i+1))<0:continue
   vals.append((e,T,V))
  if vals:out[i]=(max(q[0]for q in vals),min(q[1]for q in vals),max(q[2]for q in vals))
 return out
def pairs(n,L):
 d=fibers(n,L);out=[]
 for b,a in cwr(d,2):
  e,x,v=d[a];f,y,w=d[b];den=13*n*n
  # ceil true integral count after a rigorous upper square root
  E=(x*y-isqrt(v*w)-1+den-1)//den
  out.append((a,b,3*E-e-f,E))
 return out
def check(L):
 U,V=pairs(30,L),pairs(29,L);count=left=0;best=bestE=10000;key=None
 for a,b,f,E in U:
  for c,d,g,Q in V:
   if 4*(a+1)*(b+1)*(c+d+2)**2<(a+b)**2*max(0,c-d-1)**2+8*L**2*(a+b)*(c+d):continue
   if 4*a*b*(c+d)**2>(a+b+2)**2*(c-d+1)**2+8*L**2*(a+b+2)*(c+d+2):continue
   count+=1
   if f+g<best:best=f+g;key=a,b,c,d
   if E+Q<bestE:bestE=E+Q
   if (E+Q<=728 and f+g<=1092):left+=1
 print(L,len(U),len(V),count,left,best,bestE,key,flush=True)
 assert (len(U),len(V),count,best)==(45,120,1427,1112)
 assert best>6*182
if __name__=='__main__':check(10)
