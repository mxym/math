#!/usr/bin/env python3
"""Exact Fourier inequalities and a five-dimensional asymmetric nine-point witness."""
from fractions import Fraction as Q
import itertools
class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.a,self.b=a.a,a.b;return
        self.a=Q(a);self.b=Q(a if b is None else b)
    def __add__(self,x):
        x=I(x);return I(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,x):return self+-I(x)
    def __rsub__(self,x):return I(x)+-self
    def __mul__(self,x):
        x=I(x);v=[p*q for p in (self.a,self.b)for q in(x.a,x.b)];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I(x)
        if x.a*x.b<=0:raise ValueError('interval denominator crosses zero')
        return self*I(1/x.b,1/x.a)
    def absmax(self):return max(abs(self.a),abs(self.b))
def check(x):
    if not x:raise ArithmeticError('exact check failed')
def F(x):return x*x*(x*x-Q(1,4))
def fourier():
    roots=[]
    for z in [766044443,173648177,-939692621]:
        r=I(Q(z,10**9),Q(z+1,10**9));p=lambda t:8*t**3-6*t+1
        check(p(r.a)*p(r.b)<0);roots.append(r)
    a,b,c=roots;h=I(Q(-1,2));one=I(1)
    V=[[one,a,b,h,c],[one,b,c,h,a],[one,h,h,one,h],[one,c,a,h,b]]
    lag=[];lin=[]
    for row in V:
        d=(row[4]-row[3])/(a-h);lag.append(row[3]+d)
        lin.append([row[j]-row[3]-d*(V[1][j]-h)for j in range(3)]+[-d])
    check(lag[0].b<Q(-84,100) and lag[2].absmax()<Q(185,1000) and lag[3].absmax()<Q(185,1000))
    for i,A in enumerate(lin[0]):check(A.a>0 and lin[2][i].absmax()+lin[3][i].absmax()<7*A.a)
    value=(I(Q(3,4))+2*sum(F(lag[j])for j in [0,2,3]))/9
    check(Q(15628694,10**8)<value.a and value.b<Q(15628696,10**8))
    check(Q(84729635,10**8)<-lag[0].b and -lag[0].a<Q(84729637,10**8))
    check(len({(i+j)%9 for i,j in itertools.combinations_with_replacement((3,4,5,6),2)})==7)
    for h0 in range(9):check(sum((i+j)%9==h0 for i,j in itertools.combinations_with_replacement((3,4,5,6),2))<=2)
    print('PASS exact Fourier vertex, weak-lag slopes and rank-four support')
X=[[-10120,-8969,50012,-14684,-84264],[-10120,-8969,-50012,-14684,-84264],[17616,4082,0,-86503,-46800],[-17616,4082,0,-86503,46800],[10120,-8969,-50012,-14684,84264],[10120,-8969,50012,-14684,84264],[-11886,25633,0,60924,74095],[0,-30974,0,95082,0],[11886,25633,0,60924,-74095]]
def witness():
    n=len(X);dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    norm=[dot(v,v)for v in X];mat=[];strong=set()
    for i in range(n):
        row=[]
        for j in range(n):
            z=dot(X[i],X[j]);w=Q(z*z,norm[i]*norm[j]);row.append(w*(w-Q(1,4)))
            if i<j:
                check(z<=0 or w<Q(1,4))
                if z<0 and w>Q(1,4):strong.add((i,j))
        mat.append(row)
    path=[[6,0,4,8],[6,1,5,8],[6,2,7,3,8]]
    check(strong=={tuple(sorted((a,b)))for P in path for a,b in zip(P,P[1:])})
    def match(v):
        if not v:return True
        a=min(v)
        return any(tuple(sorted((a,b)))in strong and match(v-{a,b})for b in v-{a})
    check(all(match(set(range(n))-{i})for i in range(n)))
    # Positive LDL pivots certify the mass quadratic form; exact solve F z = 1.
    M=[v[:]+[Q(1)]for v in mat]
    for i in range(n):
        check(M[i][i]>0)
        for j in range(i+1,n):
            t=M[j][i]/M[i][i];M[j]=[a-t*b for a,b in zip(M[j],M[i])]
    z=[Q(0)]*n
    for i in reversed(range(n)):z[i]=(M[i][-1]-sum(M[i][j]*z[j]for j in range(i+1,n)))/M[i][i]
    check(min(z)>0)
    cap=1/sum(z)
    check(Q(158737,10**6)<cap<Q(158738,10**6))
    print('PASS five-dimensional theta(3,3,4) witness: 0.158737 < capacity < 0.158738')
if __name__=='__main__':fourier();witness()
