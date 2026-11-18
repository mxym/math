"""Direct exact integer checks of the Taylor coefficients; standard library.
Every real rational 2x2 test is performed before division by two, so no root
approximation or external symbolic-algebra system is used.
"""
from itertools import product
from math import comb
I=(1,0,0,1)
def add(A,B):return tuple(a+b for a,b in zip(A,B))
def sub(A,B):return tuple(a-b for a,b in zip(A,B))
def sm(x,A):return tuple(x*a for a in A)
def transp(A):a,b,c,d=A;return (a,c,b,d)
def mm(A,B):
 a,b,c,d=A;e,f,g,h=B
 return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)
def tr(A):return A[0]+A[3]
def det(A):return A[0]*A[3]-A[1]*A[2]
def topge(A,t):
 if A!=transp(A):raise ValueError('not symmetric')
 return tr(A)>=2*t or det(sub(A,sm(t,I)))<=0
def opge(A,t):return topge(mm(transp(A),A),t*t)
def trnormsq(A):return sum(a*a for a in A)+2*abs(det(A))
def require(ok): 
 if not ok:raise ValueError('exact check failed')
def run(K=14):
 checked=fail=0
 for u,v in product(range(-3,4),repeat=2):
  H=(u,0,0,v)
  for a,b,d in product(range(-2,3),(-2,0,1),range(-2,3)):
   A=(a,b,b,d);B=sub(H,A);P=[I];T=[I]
   for _ in range(K):
    P.append(mm(P[-1],A));T.append(mm(T[-1],B))
   commute=mm(A,B)==mm(B,A)
   for k in range(1,K+1):
    Q=(0,0,0,0)
    for j in range(k+1):Q=add(Q,sm(comb(k,j),mm(P[j],T[k-j])))
    X=add(Q,transp(Q)) # equals 2R_k
    sh1,sh2=sorted([abs(u)**k,abs(v)**k],reverse=True)
    require(opge(X,2*sh1) and trnormsq(X)>=(2*(sh1+sh2))**2)
    require(opge(Q,sh1) and trnormsq(Q)>=(sh1+sh2)**2)
    signed=topge(X,2*max(u**k,v**k)) and tr(X)>=2*(u**k+v**k)
    expected=(k<=4 or k%2==0 or commute or u+v>=0)
    require(signed==expected)
    if not signed:
     require(tr(X)<2*(u**k+v**k));fail+=1
    checked+=1
 require(checked==49*75*K and fail>0)
 print('exact coefficient comparisons:',checked,'; predicted signed failures:',fail)
 print('PASS')
if __name__=='__main__':run()
