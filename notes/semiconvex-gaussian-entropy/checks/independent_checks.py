#!/usr/bin/env python3
"""Independent algebraic and finite Hilbert-space audit, not a proof oracle."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import difflib, hashlib, json
import sympy as s

ROOT = Path(__file__).resolve().parent

def check(condition, name):
    if not condition:
        raise RuntimeError(name)

def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),F(0))

def vecsum(a,b,scale=F(1)):
    return [x+scale*y for x,y in zip(a,b)]

def solve(A,b):
    M=[list(row)+[x] for row,x in zip(A,b)]
    n=len(b)
    for j in range(n):
        pivot=next(i for i in range(j,n) if M[i][j])
        M[j],M[pivot]=M[pivot],M[j]
        factor=M[j][j]
        M[j]=[x/factor for x in M[j]]
        for i in range(n):
            if i!=j:
                factor=M[i][j]
                M[i]=[x-factor*y for x,y in zip(M[i],M[j])]
    return [row[-1] for row in M]

def proj(v,x):
    factor=dot(v,x)/dot(v,v)
    return [factor*y for y in v]

def mean(states,values):
    return sum((r['prob']*v for r,v in zip(states,values)),F(0))

def cond(states,values,i):
    groups={}
    for k,row in enumerate(states):
        groups.setdefault(row['past'][i],[]).append(k)
    out=[None]*len(states)
    for indices in groups.values():
        mass=sum((states[k]['prob'] for k in indices),F(0))
        value=[sum((states[k]['prob']*values[k][j] for k in indices),F(0))/mass for j in range(3)]
        for k in indices:
            out[k]=value
    return out,groups

def adaptive_case(a,delta):
    states=[]
    for bits in product([-1,1],repeat=12):
        y=bits[:3]
        noise=[bits[3+3*i:6+3*i] for i in range(3)]
        probability=F(1)
        for sign in y:
            probability*=F(1,3) if sign==1 else F(2,3)
        for i,pp in enumerate([F(3,4),F(4,5),F(2,3)]):
            for sign in noise[i]:
                probability*=pp if sign==1 else 1-pp
        z=[tuple(y[j]*noise[i][j] for j in range(3)) for i in range(3)]
        states.append({'prob':probability,'W':[F(x+3) for x in y],
                       'past':[z[0],z[0]+z[1]],
                       'controls':[[F(1),F(z[0][0]+2*z[0][1]),F(z[0][2])],
                                   [F(z[0][0]+z[1][1]),F(1),F(z[0][1]*z[1][2])]]})
    check(sum((r['prob'] for r in states),F(0))==1,'finite state law')
    W=[r['W'] for r in states]
    e0,_=cond(states,W,0)
    e1,_=cond(states,W,1)
    alpha=[a/(a+j*delta) for j in range(3)]
    v0=[[alpha[2]*w+(alpha[0]-alpha[1])*x+(alpha[1]-alpha[2])*y
         for w,x,y in zip(ww,xx,yy)] for ww,xx,yy in zip(W,e0,e1)]
    ev=[cond(states,v0,i)[0] for i in range(2)]
    g=[[vecsum(v,e,-1) for v,e in zip(v0,ev[i])] for i in range(2)]
    vc=[]
    for row in states:
        A=[[F(a+2*delta) if j==k else F(0) for k in range(3)] for j in range(3)]
        for direction in row['controls']:
            norm=dot(direction,direction)
            A=[[x-delta*direction[j]*direction[k]/norm for k,x in enumerate(arow)] for j,arow in enumerate(A)]
        vc.append(solve(A,[a*x for x in row['W']]))
    truecost=[]; compcost=[]; cross=[]
    for k,row in enumerate(states):
        w,v,h=row['W'],vc[k],v0[k]
        check([a*(x-y) for x,y in zip(w,h)]==[delta*(x+y) for x,y in zip(g[0][k],g[1][k])],
              'comparison normal equation')
        truecost.append(a*dot(vecsum(w,v,-1),vecsum(w,v,-1))+
                        delta*sum((dot(vecsum(v,proj(d,v),-1),vecsum(v,proj(d,v),-1)) for d in row['controls']),F(0)))
        compcost.append(a*dot(vecsum(w,h,-1),vecsum(w,h,-1))+
                        delta*(dot(g[0][k],g[0][k])+dot(g[1][k],g[1][k])))
        cross.append(sum((dot(v,proj(row['controls'][i],g[i][k])) for i in range(2)),F(0)))
    M=mean(states,truecost); M0=mean(states,compcost)
    normW=mean(states,[dot(w,w) for w in W])
    check(M==a*(normW-mean(states,[dot(w,v) for w,v in zip(W,vc)])),'true inverse identity')
    spectral=sum((a*a*delta/((a+i*delta)*(a+(i+1)*delta))*
                  (normW-mean(states,[dot(v,v) for v in ee])) for i,ee in enumerate([e0,e1])),F(0))
    check(M0==spectral,'spectral comparison identity')
    check(M>=M0-2*delta*mean(states,cross),'signed dual comparison')
    check(mean(states,[dot(v,v) for v in vc])<=normW,'true minimizer contraction')
    for i in range(2):
        centered,groups=cond(states,g[i],i)
        check(all(v==[F(0)]*3 for v in centered),'conditional centering')
        for indices in groups.values():
            mass=sum((states[k]['prob'] for k in indices),F(0))
            cov=[[sum((states[k]['prob']*g[i][k][j]*g[i][k][l] for k in indices),F(0))/mass for l in range(3)] for j in range(3)]
            check(all(cov[j][l]==0 for j in range(3) for l in range(3) if j!=l),'three-copy covariance diagonal')
            direction=states[indices[0]]['controls'][i]
            projected=sum((states[k]['prob']*dot(proj(direction,g[i][k]),proj(direction,g[i][k])) for k in indices),F(0))/mass
            check(projected<=max(cov[j][j] for j in range(3)),'adaptive rank-one covariance bound')
    return {'a':str(a),'delta':str(delta),'states':len(states),'true_min':str(M),'comparison_min':str(M0)}

def symbolic_checks():
    t,r,k,d,u=s.symbols('t r k d u',positive=True)
    A=k+1/t; mu=t*u/(t+r); v=t*r/(t+r)
    predicted=-A*mu+d*(mu**3+3*mu*v)
    poly=s.Poly(s.expand(predicted**2),u)
    direct=0
    for (power,),coef in poly.terms():
        direct+=coef*s.factorial2(power-1)*(t+r)**(power/2) if power else coef
    target=(A-3*d*t)**2*t**2/(t+r)+6*d*d*t**6/(t+r)**3
    # Avoid floating exponents in the independent moment integration.
    direct=sum((coef*s.factorial2(power-1)*(t+r)**(power//2) if power else coef
                for (power,),coef in poly.terms()),s.Integer(0))
    check(s.simplify(direct-target)==0,'symbolic direct cubic prediction')
    z=s.symbols('z',positive=True)
    entropy=s.log(1+z/t)-s.log(1-k*z)+k*z*(1+k*t)/(1-k*z)
    integrand=(1+k*t)**2/((t+z)*(1-k*z)**2)
    check(s.simplify(s.diff(entropy,z)-integrand)==0,'sharp weighted derivative')
    # Independent exact m=3 resolvent weights for an abstract spectral decomposition.
    a,dd=s.symbols('a dd',positive=True)
    for j in range(4):
        telescope=sum((a*a*dd/((a+i*dd)*(a+(i+1)*dd)) for i in range(j)),s.Integer(0))
        check(s.simplify(telescope-a*j*dd/(a+j*dd))==0,'spectral penalty telescope')
    delta,sp,sq=s.symbols('delta sp sq',positive=True)
    vp=1+delta*sp; vq=1+delta*sq
    kl=(s.log(vq/vp)+vp/vq-1)/2
    check(s.simplify(s.diff(kl,delta).subs(delta,0))==0,'matching Gaussian means remove linear entropy cost')
    check(s.simplify(s.diff(kl,delta,2).subs(delta,0)/2-(sp-sq)**2/4)==0,'Gaussian entropy cost second-order coefficient')
    return ['direct cubic prediction','sharp weighted derivative','four spectral penalty telescopes',
            'zero first-order matching-means cost','exact second-order matching-means cost']

def patch_and_hashes():
    old=(ROOT/'entropy.tex').read_text()
    needle=r'\E e^{\theta|X|^2}\le(1-2\theta/a)^{-k/2}\quad(2\theta<a).'
    replacement=r'\E e^{\theta|X|^2}\le(1-2\theta/a)^{-k/2}\quad(0\le\theta<a/2).'
    check(old.count(needle)==1,'unique source patch target')
    new=old.replace(needle,replacement)
    patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),
                                      fromfile='entropy.tex',tofile='entropy.corrected.tex'))
    (ROOT/'square_exponential_domain.patch').write_text(patch)
    (ROOT/'entropy.corrected.tex').write_text(new)
    return {'original_sha256':hashlib.sha256(old.encode()).hexdigest(),
            'corrected_sha256':hashlib.sha256(new.encode()).hexdigest(),
            'patch_sha256':hashlib.sha256(patch.encode()).hexdigest()}

def main():
    symbolic=symbolic_checks()
    finite=[]
    for a,delta in [(F(1,3),F(1,4)),(F(2),F(3,5))]:
        finite.append(adaptive_case(a,delta))
    finitegap=1+F(109,128)-F(15625,4096)*F(5,12)-F(5,12288)
    check(finitegap==F(12863,49152)>0,'finite quartic counterexample exact gap')
    # Negative-theta counterexample: a=1, variance=1/2, theta=-1.
    check(F(1,2)>F(1,3),'negative-theta square moment counterexample after squaring')
    result={'status':'PASS','symbolic_checks':symbolic,'finite_adaptive_cases':finite,
            'finite_quartic_certificate_gap':str(finitegap),
            'literal_lemma_counterexample':{'a':1,'variance':'1/2','theta':-1,
                                           'lhs':'1/sqrt(2)','purported_rhs':'1/sqrt(3)'},
            'patch':patch_and_hashes(),
            'scope':'Independent finite/symbolic checks; analytic audit supplies the universal argument.'}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
