#!/usr/bin/env python3
"""Independent Gaussian-rational checks; finite algebra only, not analytic proof."""
from fractions import Fraction as Q
import json
def req(v,s):
    if not v: raise RuntimeError(s)
def g(x=0,y=0): return (Q(x),Q(y))
Z=g()
def ga(x,y): return (x[0]+y[0],x[1]+y[1])
def gn(x): return (-x[0],-x[1])
def gm(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def gc(x): return (x[0],-x[1])
def gs(x): return x[0]*x[0]+x[1]*x[1]
def su(xs):
    v=Z
    for x in xs: v=ga(v,x)
    return v
def eye(n): return [[g(i==j) for j in range(n)] for i in range(n)]
def zero(n,m): return [[Z for _ in range(m)] for _ in range(n)]
def adj(a): return [[gc(a[j][i]) for j in range(len(a))] for i in range(len(a[0]))]
def trans(a): return [list(r) for r in zip(*a)]
def mat(a,b): return [[su(gm(x,y) for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b): return [[ga(x,y) for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a): return [[gn(x) for x in r] for r in a]
def sc(a,c): return [[gm(x,g(c)) for x in r] for r in a]
def hs(a): return sum(gs(x) for r in a for x in r)
def tr(a): return su(a[i][i] for i in range(len(a)))
def stereographic(n,m,seed):
    v=[Q(((i+1)*7+seed*11)%19-9,13) for i in range(2*n*m-1)]
    ss=sum(x*x for x in v)
    w=[2*x/(1+ss) for x in v]+[(1-ss)/(1+ss)]
    a=[[g(w[2*(i*m+j)],w[2*(i*m+j)+1]) for j in range(m)] for i in range(n)]
    req(hs(a)==1,'complex rational normalization')
    return a
def house(n,seed):
    v=stereographic(n,1,seed)
    u=add(eye(n),sc(mat(v,adj(v)),-2))
    req(mat(adj(u),u)==eye(n),'rational unitary')
    return u
def coeff(a,x,y,n):
    xp,yp=adj(x),adj(y)
    power=eye(n); out=[[],[],[],[]]
    for j in range(n):
        for o,l,r in zip(out,[xp,yp,yp,xp],[x,y,x,y]): o.append(mat(mat(l,power),r))
        power=mat(power,a)
    req(power==zero(n,n),'finite nilpotent Laurent series')
    return out
def block(a,x,y,n,mu,upper,gamma):
    p,q,m,l=coeff(a,x,y,n)
    rx,ry=mat(x,adj(x)),mat(y,adj(y))
    purity_x,purity_y=hs(rx),hs(ry); overlap=hs(m[0])
    req(tr(mat(rx,ry))==g(overlap),'complex density overlap')
    req(adj(l[0])==m[0],'complex constant Fourier term')
    energy=sum(hs(c) for c in m)
    up=4*hs(p[0])+2*sum(hs(c) for c in p[1:])
    uq=4*hs(q[0])+2*sum(hs(c) for c in q[1:])
    cross=4*overlap+sum(hs(c) for c in m[1:])+sum(hs(c) for c in l[1:])
    slack=up+uq-2*cross
    req(cross==energy+3*overlap+sum(hs(c) for c in l[1:]),'offdiagonal complex Parseval')
    d=add(rx,neg(ry)); powers=[eye(n)]
    for k in range(1,n): powers.append(mat(powers[-1],a))
    h={0:sc(eye(n),2)}
    for k in range(1,n): h[-k]=powers[k]; h[k]=adj(powers[k])
    trace_sum=su(tr(mat(mat(mat(h[k],d),h[-k]),d)) for k in h)
    req(trace_sum==g(slack),'complex reduced-density Laurent trace')
    req(hs(d)==purity_x+purity_y-2*overlap,'complex density distance')
    req(slack>=mu*mu*hs(d),'uniform Hermitian lower bound')
    cap=min(mu*mu,Q(3))
    req(slack+6*overlap>=cap*(purity_x+purity_y),'rank-free capped slack')
    req(energy*energy<=upper**4*purity_x*purity_y,'purity energy square inequality')
    dp,dq=4*energy/gamma**2-up,4*energy/gamma**2-uq
    req(2*energy*(4/gamma**2-1)==dp+dq+slack+6*overlap+2*sum(hs(c) for c in l[1:]),'exact full complex deficit')
    return dp,dq,energy,p,q,m
def functional(left,b,right,c):
    k=mat(mat(adj(left),b),right)
    return su(gm(k[i][j],c[i][j]) for i in range(len(c)) for j in range(len(c)))
generic=0
for n,m in [(2,1),(2,3),(3,2),(4,3)]:
    for seed in range(1,6):
        u=house(n,seed); a=zero(n,n); t=Q(1,8)
        for j in range(n-1): a[j][j+1]=g(t)
        a=mat(mat(u,a),adj(u))
        x,y=stereographic(n,m,seed+1),stereographic(n,m,seed+9)
        tail=sum(t**j for j in range(1,n)); mu=2-2*tail
        block(a,x,y,n,mu,1+tail,Q(3,2)); generic+=1
singular=ordered=0
for k,m in [(1,1),(2,2),(3,2),(2,3)]:
    n=2*k
    for seed in range(1,6):
        for t in [Q(1,4),Q(1),Q(7,4)]:
            a=zero(n,n)
            for j in range(k): a[2*j][2*j+1]=g(t)
            small=stereographic(k,m,seed); x=zero(n,m)
            for j in range(k): x[2*j+1]=small[j]
            c=house(m,seed+5)
            y=mat(sc(mat(a,x),1/t),trans(c))
            req(hs(y)==1,'actual entangled left singular vector')
            req(mat(sc(mat(adj(a),y),1/t),trans(adj(c)))==x,'actual adjoint singular relation')
            dp,dq,energy,p,q,mc=block(a,x,y,n,2-t,1+t,t)
            req(dp>=0 and dq>=0,'actual singular-pair dual slacks')
            test=[[g(Q((i+j+seed)%7,9),Q((2*i-j+seed)%5,11)) for j in range(m)] for i in range(m)]
            req(functional(y,a,x,mat(c,test))==gm(g(t),functional(x,eye(n),x,test)),'ordered FG complex pairing')
            req(functional(y,a,x,mat(test,c))==gm(g(t),functional(y,eye(n),y,test)),'ordered GF complex pairing')
            singular+=1; ordered+=2
ellipse=0
for alpha in [Q(0),Q(1,4),Q(3,4),Q(15,16)]:
    for m in [1,2,3]:
        for degree in [1,3,7]:
            cs=[[[g(Q((i+2*j+k+3)%7,9),Q((2*i-j+3*k+5)%11,13)) for j in range(m)] for i in range(m)] for k in range(degree+1)]
            # h=lambda+alpha/lambda; b_k(h)=lambda^k+alpha^k lambda^-k.
            lower=sum(hs(c) for c in cs)
            boundary=lower+sum(alpha**(2*k)*hs(cs[k]) for k in range(1,degree+1))
            upper=hs(cs[0])+2*sum(hs(c) for c in cs[1:])
            req(lower<=boundary<=upper,'exact ellipse complex coefficient inequality')
            ellipse+=1
print(json.dumps({'status':'PASS','arithmetic':'Gaussian rationals using fractions.Fraction','generic_complex_nilpotent_density_cases':generic,'actual_entangled_complex_singular_pair_cases':singular,'separately_ordered_complex_product_tests':ordered,'exact_ellipse_coefficient_cases':ellipse,'scope':'Independent finite algebra and coefficient examples; universal analytic proof is audited separately.'},sort_keys=True,indent=2))

