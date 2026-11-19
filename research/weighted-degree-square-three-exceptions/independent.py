"""Exact replay of finite identities. No imports from the author's checker."""
from fractions import Fraction as Q
from itertools import product,combinations
from math import comb,prod,factorial
from collections import defaultdict

def ok(x,msg):
    if not x:raise ArithmeticError(msg)

def cutoff(a,A,h,B):
    m=len(h);pairs=list(combinations(range(m),2))
    best=0
    for bits in product(range(2),repeat=m-1):
        s=(1,)+bits
        fixed=sum(w for w,(i,j) in zip(B,pairs) if s[i]!=s[j])
        for v in range(a+1):
            cut=A*v*(a-v)+sum(x*((a-v) if z else v) for x,z in zip(h,s))+fixed
            best=max(best,cut)
    return best

def total_degrees(a,A,h,B):
    m=len(h);pairs=list(combinations(range(m),2))
    deg=[a*x for x in h]
    for w,(i,j) in zip(B,pairs):deg[i]+=w;deg[j]+=w
    d=(a-1)*A+sum(h)
    W=A*comb(a,2)+a*sum(h)+sum(B)
    return W,a*d*d+sum(x*x for x in deg)

def clipped(t,y):
    a=t+2+sum(y);h=[1+t+i for i in y];z=t*(t+1)//2
    B=[v*w-z for v,w in combinations(h,2)]
    p=y[2]+1
    # plus exceptions 0 and 1, minus exception 2; exactly p ordinary vertices plus.
    cut=p*(a-p)+(a-p)*(h[0]+h[1])+p*h[2]+B[1]+B[2]
    ok(0<=p<=a and cut==cutoff(a,1,h,B),('cut',t,y))
    W,D=total_degrees(a,1,h,B)
    return 8*W*cut-4*W*W-D

def sym(t,y):
    S=sum(y);P=sum(x*z for x,z in combinations(y,2));R=prod(y);U=S*S-3*P
    ok(U>=0,('delta',y))
    return 6*(S*S+P)*U+(8*t+6)*S**3+(28*t+30)*S*U+(32*t*t+60*t+24)*S*S+(16*t*t+48*t+30)*U+(24*S+36*t+54)*R+12*(t+1)*(4*t*t+7*t+2)*S+24*t*(t+1)**2*(t+2)

def monomial_coefficients(vals,m=4,maxdeg=4):
    # Total-degree multivariate Newton interpolation, converting each falling
    # factorial to the ordinary monomial basis. Uses exactly C(m+d,d) points.
    poly=defaultdict(Q)
    for al in vals:
        coeff=sum((-1)**(sum(al)-sum(b))*prod(comb(a,x) for a,x in zip(al,b))*vals[b] for b in product(*(range(a+1) for a in al)))
        coef=[Q(coeff,prod(factorial(a) for a in al))]
        factors=[]
        for a in al:
            p=[1]
            for j in range(a):
                p=[(p[i-1] if i else 0)-(j*p[i] if i<len(p) else 0) for i in range(len(p)+1)]
            factors.append(p)
        for deg in product(*(range(len(row)) for row in factors)):
            poly[deg]+=coef[0]*prod(row[i] for row,i in zip(factors,deg))
    return {k:v for k,v in poly.items() if v}

def partitions(n,last):
    if n==0:yield ()
    for k in range(min(n,last),0,-1):
        for rest in partitions(n-k,k):yield (k,)+rest

def main():
    vals={};ninterp=0
    for q in product(range(5),repeat=4):
        t=q[0]+1;e=q[1:]
        gap=clipped(t,e)
        ok(3*gap==sym(t,e),('symmetric SOS',t,e))
        # Unsorted symmetric branch above; sorted increments in frozen script below.
        if sum(q)<=4:
            u,i,j,k=q;x=(i+j+k,j+k,k)
            vals[q]=clipped(t,x)
        ninterp+=1
    coeff=monomial_coefficients(vals)
    ok(len(coeff)==70 and min(coeff.values())==2 and max(coeff.values())==516 and coeff[(0,0,0,0)]==96,'Newton coefficients')
    print('Complete 5^4 interpolation grid for 8-term positive identity:',ninterp,'Exact total-degree Newton grid:',len(vals),'reconstructed sorted coefficients:',len(coeff),'range 2..516, constant 96')
    tests=tri=0
    for m in (2,3):
        for a in range(2,8):
            for tup in product(range(3),repeat=1+m+comb(m,2)):
                A=tup[0];h=tup[1:1+m];B=tup[1+m:];W,D=total_degrees(a,A,h,B);cut=cutoff(a,A,h,B)
                ok(8*W*cut>=4*W*W+D,(a,tup,'ineq'))
                if m==3 and A>0 and min(h)==0 and min(B)>0:
                    residual=[b-min(B) for b in B]
                    ok(cut==cutoff(a,A,h,residual)+2*min(B),(a,tup,'strip'))
                    tri+=1
                tests+=1
    print('All symmetric 2- and 3-exception test graphs A,H,B=0,1,2 and a=2..7:',tests,'strictly nontrivial simultaneous triangle strip checks:',tri)
    pcount=0
    for n in range(2,30):
        for x in partitions(n,n):
            if len(x)<=1:continue
            Q2=sum(i*i for i in x);S3=sum(i**3 for i in x);S4=sum(i**4 for i in x)
            r=0
            for i in x:r=abs(r-i)
            ok(n*r*r<=S3,('greedy',x))
            ok((n*n-Q2)*r*r<=2*n*S3-S4-Q2*Q2,('product',x))
            pcount+=1
    print('Sorted integer partitions in the independent rank-one check:',pcount)
    print('PASS')
if __name__=='__main__':main()
