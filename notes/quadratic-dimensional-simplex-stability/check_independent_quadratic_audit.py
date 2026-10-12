#!/usr/bin/env python3
"""Independent exact rational regressions, supplementary to the analytic audit.
No proof-author check code is imported. The replay runner executes this script in a temporary copy.
"""
import hashlib, itertools, json, math, pathlib
import sympy as s
R=s.Rational
ROOT=pathlib.Path(__file__).resolve().parent

def check(ok, desc):
    if not ok: raise RuntimeError(desc)

def lift(xs): return s.Matrix.hstack(*[x.col_join(s.ones(1,1)) for x in xs])
def det(xs): return abs(lift(xs).det())
def pos(x): return max(x,0)
def colnorm(A): return max(sum(abs(x) for x in A[:,i]) for i in range(A.cols))

def case(d,t):
    n=d+1; basis=[s.eye(d)[:,i] for i in range(d)]
    verts=basis+[t*x for x in basis]
    all_s=[(det([verts[i] for i in ix]),ix) for ix in itertools.combinations(range(2*d),n)]
    maxdet=max(x[0] for x in all_s)
    check(maxdet==1-t,'maximum simplex determinant')
    maxsets=[ix for D,ix in all_s if D==maxdet]
    # Any one original maximum defines the origin used by the cone law.
    S=[verts[i] for i in maxsets[-1]]
    z=sum(S,s.zeros(d,1))/n
    v=(1-t**d)/math.factorial(d)
    X=[-basis[i]/z[i] for i in range(d)]
    probs=[z[i]*(1-t**(d-1))/(1-t**d) for i in range(d)]
    top=1-sum(z); bottom=sum(z)-t
    X += [s.ones(d,1)/top,-s.ones(d,1)/bottom]
    probs += [top/(1-t**d),bottom*t**(d-1)/(1-t**d)]
    check(sum(probs)==1,'cone probability mass')
    check(sum([p*x for p,x in zip(probs,X)],s.zeros(d,1))==s.zeros(d,1),'cone centering')
    centered=[x-z for x in verts]
    def hK(y): return max((x.dot(y) for x in centered))
    def N(y): return hK(y)+hK(-y)
    check(all(hK(x)==1 for x in X),'polar boundary support')
    check(all(N(x)<=n for x in X),'intrinsic support radius')
    check(all(N(x-y)<=2*n for x in X for y in X),'intrinsic support diameter')
    A=sum(math.factorial(d)*abs(s.Matrix.hstack(*[X[i] for i in ix]).det())*s.prod(probs[i] for i in ix) for ix in itertools.combinations(range(d+2),d))
    BB=sum(math.factorial(n)*det([X[i] for i in ix])*s.prod(probs[i] for i in ix) for ix in itertools.combinations(range(d+2),n))
    D=BB-A; excess=D/(n*A)
    check(D>=0 and A>0 and BB>0,'first moments positive')
    check(D/BB==n*excess/(1+n*excess),'D/B exact correction')
    Delta=max(N(x-y) for x in X for y in X)
    candidates=[]
    for ix in itertools.combinations(range(d+2),n):
        anchors=[X[i] for i in ix]; L=lift(anchors)
        if L.det()==0: continue
        Li=L.inv(); Hratio=0; hh=0; pp=[s.Integer(0)]*n
        for p,x in zip(probs,X):
            a=list(Li*x.col_join(s.ones(1,1)))
            witness=sum(min(1,pos(-aa)) for aa in a)
            witness+=sum(min(pos(a[i]),pos(a[j]))+min(pos(-a[i]),pos(-a[j])) for i in range(n) for j in range(i+1,n))
            Hratio+=p*witness
            ii=max(range(n),key=lambda i:a[i])
            distance=N(x-anchors[ii]);hh+=p*distance;pp[ii]+=p
            check(distance<=Delta*witness,'pointwise clipped witness')
        candidates.append((Hratio,hh,ix,pp,Li))
    Hratio,hh,ix,pp,Li=min(candidates,key=lambda x:x[0])
    check(Hratio<=n*(n+1)*D/(2*BB),'volume-weighted existence')
    check(hh<=Delta*Hratio,'integrated assignment')
    C=n**3*(n+1)
    check(hh<=C*excess/(1+n*excess),'intrinsic assignment coefficient')
    projections=0; bridge_checks=0
    if hh<R(1,2*d):
        anchors=[X[i] for i in ix]
        lam=list(Li*s.zeros(d,1).col_join(s.ones(1,1)))
        check(min(lam)>0,'strict origin containment')
        q=[]
        for i in range(n):
            M=s.Matrix.vstack(*[anchors[j].T for j in range(n) if j!=i])
            q.append(M.inv()*s.ones(d,1))
        Pvol=det(q)/math.factorial(d)
        c=sum([pp[i]*anchors[i] for i in range(n)],s.zeros(d,1))
        r=2*d*hh
        check(N(c)<=hh,'assigned mean norm')
        check(all(pp[i]-lam[i]==-lam[i]*q[i].dot(c) for i in range(n)),'weight correction identity')
        check(all(pp[i]>=(1-r)*lam[i] for i in range(n)),'multiplicative weights')
        zz=sum(p*(max(y.dot(x) for y in q)-1) for p,x in zip(probs,X))
        check(0<=zz<=r,'mixed-volume excess')
        check(Pvol/v<=(1+zz)**d,'Minkowski volume bound')
        for tup in itertools.product([-1,0,1],repeat=d):
            if not any(tup): continue
            u=s.Matrix(tup)
            fK=sum(p*abs(u.dot(x)) for p,x in zip(probs,X))
            fP=sum(lam[i]*abs(u.dot(anchors[i])) for i in range(n))
            piK=(sum(abs(x) for x in tup)*(1-t**(d-1))+abs(sum(tup))*(1+t**(d-1)))/(2*math.factorial(d-1))
            check(fK==2*piK/(d*v),'Cauchy normalization')
            check((1-r)*fP<=(1+R(d,2)*hh)*fK,'normalized multiplicative conversion')
            piP=d*Pvol*fP/2
            relative=1-piK/piP
            check(0<=relative<=3*d*d*hh,'relative denominator and coefficient')
            projections+=1
    # The enclosing ORIGINAL untruncated simplex has exact sup relative
    # deficit t^(d-1), attained when sum(u)=0. Check every vertex-set maximum.
    rho=t
    for sel in maxsets:
        W=lift([verts[i] for i in sel]); Winv=W.inv()
        alphas=[Winv*x.col_join(s.ones(1,1)) for x in verts]
        E=n*max(0,-min(a for aa in alphas for a in aa))
        check(E==n*t,'every vertex-set maximum and original centroid')
        check(E<=16*n*n*rho,'global bridge')
        if rho<=R(1,16*n): check(E<=8*n*rho,'local bridge')
        bridge_checks+=1
    return dict(d=d,t=str(t),e=str(excess),assignment_h=str(hh),maximum_vertex_sets=len(maxsets),projection_directions_checked=projections,bridge_checks=bridge_checks)

rows=[case(d,t) for d in (3,4,5) for t in (R(1,1000),R(1,100),R(1,2))]
# Exact endpoint matrices test the matching bootstrap including beta=1/2's gate.
for n in range(4,31):
    rho=R(1,16*n); eta=2*n*rho
    check(eta==R(1,8),'eta endpoint')
    check(4*eta<1-eta,'matching strict contradiction endpoint')
    check(4*n*rho/(1-8*n*rho)==R(1,2),'inverse entry endpoint')
    check(4*rho/(1-8*rho)<=8*rho,'final local entry bound')
# Independent symbolic clearing of denominator for Bernoulli/union estimate
# is covered analytically in audit; finite rational r values check arithmetic.
relative_checks=0
for d in (3,4,10,50):
    for j in range(100):
        r=R(j,100)
        actual=1-(1-r)/((1+r)**d*(1+r/4))
        check(actual<=(d+R(5,4))*r,'relative product inequality')
        check(2*d*(d+R(5,4))<=3*d*d,'coefficient comparison')
        relative_checks+=1
# Public derivative and exact historical source pins match the reviewed payload.
manifest=json.loads((ROOT/'SOURCE_PINS.json').read_text())
for row in manifest['sources']:
    p=ROOT/row['path']
    check(hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],'public source pin mismatch: '+row['path'])
out=dict(status='PASS',exact_convex_body_cases=rows,relative_rational_checks=relative_checks,endpoint_dimensions='3..29',source_hashes_unchanged=True,scope='Finite exact regression only; unrestricted result established by written analytic audit.')
(ROOT/'independent_exact_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
