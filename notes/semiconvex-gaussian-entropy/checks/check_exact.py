#!/usr/bin/env python3
"""Exact supporting checks for entropy.tex; universal analytic proofs are written."""
from fractions import Fraction as F
from itertools import product
from decimal import Decimal, localcontext
import json

def require(condition, description):
    if not condition:
        raise RuntimeError(description)

def dot(x, y):
    return sum((a*b for a,b in zip(x,y)), F(0))

def add(x, y, sign=1):
    return [a+sign*b for a,b in zip(x,y)]

def scale(x, a):
    return [a*b for b in x]

def matvec(a, x):
    return [dot(row,x) for row in a]

def matrix_add(a, b, sign=1):
    return [add(x,y,sign) for x,y in zip(a,b)]

def matrix_scale(a, c):
    return [scale(row,c) for row in a]

IDENTITY = [[F(1),F(0)],[F(0),F(1)]]

def inverse2(a):
    determinant=a[0][0]*a[1][1]-a[0][1]*a[1][0]
    require(determinant>0, 'positive finite control matrix')
    return [[a[1][1]/determinant,-a[0][1]/determinant],
            [-a[1][0]/determinant,a[0][0]/determinant]]

def projection(slope):
    denominator=1+slope*slope
    return [[1/denominator,slope/denominator],
            [slope/denominator,slope*slope/denominator]]

def gaussian_moment(power, variance):
    if power % 2:
        return F(0)
    value=F(1)
    for j in range(1,power,2):
        value*=j*variance
    return value

def prediction_case(t, kappa, radius, r):
    a=kappa+1/t
    cubic=4/radius**4
    alpha=t/(t+r)
    posterior_variance=t*r/(t+r)
    # Direct conditional Gaussian cubic moment, squared and averaged under U.
    linear=alpha*(-a+3*cubic*posterior_variance)
    third=cubic*alpha**3
    direct=(linear*linear*gaussian_moment(2,t+r)
            +2*linear*third*gaussian_moment(4,t+r)
            +third*third*gaussian_moment(6,t+r))
    hermite=(a-3*cubic*t)**2*t*t/(t+r)+6*cubic*cubic*t**6/(t+r)**3
    require(direct==hermite, 'Gaussian cubic prediction = Hermite formula')
    information=a*a*t-24*a*t*t/radius**4+240*t**3/radius**8
    require(F(0)<=direct<=information, 'conditional prediction contraction')
    if r==0:
        require(direct==information, 'initial prediction = initial score energy')

def weighted_derivative_case(t,kappa,r):
    if 1-kappa*r<=0:
        return False
    derivative=1/(t+r)+kappa/(1-kappa*r)+kappa*(1+kappa*t)/(1-kappa*r)**2
    integrand=(1+kappa*t)**2/((t+r)*(1-kappa*r)**2)
    require(derivative==integrand, 'sharp entropy-limit derivative = weighted prediction')
    return True

def finite_fixture():
    states=[]
    for signs in product([-1,1],repeat=6):
        y1,y2,e01,e02,e11,e12=signs
        probability=F(1,4)
        for sign in [e01,e02]:
            probability*=F(3,4) if sign==1 else F(1,4)
        for sign in [e11,e12]:
            probability*=F(2,3) if sign==1 else F(1,3)
        f0=(y1*e01,y2*e02)
        f1=f0+(y1*e11,y2*e12)
        states.append({'probability':probability,'W':[F(y1),F(y2)],'f0':f0,'f1':f1})
    require(sum((s['probability'] for s in states),F(0))==1,'finite probability normalization')
    return states

def expectation(states, values):
    return sum((s['probability']*v for s,v in zip(states,values)),F(0))

def conditional(states, values, level):
    totals={}
    for s,v in zip(states,values):
        key=s[level]
        if key not in totals:
            totals[key]=[F(0),[F(0) for _ in v]]
        totals[key][0]+=s['probability']
        totals[key][1]=add(totals[key][1],scale(v,s['probability']))
    return [scale(totals[s[level]][1],1/totals[s[level]][0]) for s in states]

def finite_minimum_case(a,delta,slope):
    states=finite_fixture()
    W=[s['W'] for s in states]
    e0=conditional(states,W,'f0')
    e1=conditional(states,W,'f1')
    alpha=[a/(a+j*delta) for j in range(3)]
    v0=[add(add(scale(w,alpha[2]),scale(x,alpha[0]-alpha[1])),
            scale(y,alpha[1]-alpha[2])) for w,x,y in zip(W,e0,e1)]
    predicted_v0=[conditional(states,v0,'f0'),conditional(states,v0,'f1')]
    residual=[[add(v,p,-1) for v,p in zip(v0,pred)] for pred in predicted_v0]
    controls=[]
    for s in states:
        p0=projection(slope*s['f0'][0]*s['f0'][1])
        p1=projection(slope*s['f1'][0]*s['f1'][2]*s['f1'][3])
        controls.append([p0,p1])
    vstar=[]
    for s,projections in zip(states,controls):
        q=[matrix_add(IDENTITY,p,-1) for p in projections]
        precision=matrix_add(matrix_scale(IDENTITY,a),
                             matrix_scale(matrix_add(q[0],q[1]),delta))
        vstar.append(scale(matvec(inverse2(precision),s['W']),a))
    true_cost=[]; comparison_cost=[]; cross=[[],[]]
    for j,s in enumerate(states):
        w,v,vcomp=s['W'],vstar[j],v0[j]
        require(scale(add(w,vcomp,-1),a)==scale(add(residual[0][j],residual[1][j]),delta),
                'comparison normal equation pointwise')
        qs=[matrix_add(IDENTITY,p,-1) for p in controls[j]]
        true_cost.append(a*dot(add(w,v,-1),add(w,v,-1))
                         +delta*sum((dot(matvec(q,v),matvec(q,v)) for q in qs),F(0)))
        comparison_cost.append(a*dot(add(w,vcomp,-1),add(w,vcomp,-1))
                               +delta*(dot(residual[0][j],residual[0][j])
                                       +dot(residual[1][j],residual[1][j])))
        for i in range(2):
            cross[i].append(dot(v,matvec(controls[j][i],residual[i][j])))
    information=expectation(states,[dot(w,w) for w in W])
    true_min=expectation(states,true_cost)
    comparison_min=expectation(states,comparison_cost)
    resolvent_min=a*(information-expectation(states,[dot(w,v) for w,v in zip(W,vstar)]))
    spectral_min=(a*a*delta/(a*(a+delta))
                  *(information-expectation(states,[dot(x,x) for x in e0]))
                  +a*a*delta/((a+delta)*(a+2*delta))
                  *(information-expectation(states,[dot(x,x) for x in e1])))
    require(true_min==resolvent_min, 'true minimum = inverse precision identity')
    require(comparison_min==spectral_min, 'nested projection spectral minimum')
    require(true_min>=comparison_min-2*delta*sum((expectation(states,x) for x in cross),F(0)),
            'adaptive dual comparison with signed exact cross term')
    require(expectation(states,[dot(v,v) for v in vstar])<=information,'true minimizer contraction')
    for i,level in enumerate(['f0','f1']):
        gi=residual[i]
        require(all(x==[F(0),F(0)] for x in conditional(states,gi,level)),
                'future residuals conditionally centered')
        groups={}
        for j,s in enumerate(states):
            groups.setdefault(s[level],[]).append(j)
        for indices in groups.values():
            mass=sum((states[j]['probability'] for j in indices),F(0))
            covariance=[[sum((states[j]['probability']*gi[j][k]*gi[j][l]
                              for j in indices),F(0))/mass for l in range(2)] for k in range(2)]
            require(covariance[0][1]==covariance[1][0]==0,'conditional copy covariance block diagonal')
            require(max(covariance[0][0],covariance[1][1])<=1,'conditional score second moment bound')
            projected=sum((states[j]['probability']*dot(matvec(controls[j][i],gi[j]),
                           matvec(controls[j][i],gi[j])) for j in indices),F(0))/mass
            require(projected<=max(covariance[0][0],covariance[1][1]),'adaptive rank-one covariance loss')

def main():
    tvalues=[F(1,4),F(1,2),F(1),F(3)]
    kvalues=[F(0),F(1,2),F(1),F(2)]
    rvalues=[F(0),F(1,8),F(1,2),F(2)]
    prediction_count=0; derivative_count=0; minimum_count=0; kernel_count=0
    for t,k,r in product(tvalues,kvalues,rvalues):
        derivative_count+=int(weighted_derivative_case(t,k,r))
        for radius in [F(2),F(4),F(8)]:
            prediction_case(t,k,radius,r)
            prediction_count+=1
    for a,delta,slope in product([F(1,4),F(1),F(3),F(5)],
                                 [F(1,8),F(1,2),F(2)],
                                 [F(1,2),F(1),F(2)]):
        finite_minimum_case(a,delta,slope)
        minimum_count+=1
    for a,delta,m in product([F(1,4),F(1),F(3),F(5)],
                            [F(1,8),F(1,2),F(2)],[1,2,4,9]):
        total=sum((delta/((a+i*delta)*(a+(i+1)*delta)) for i in range(m)),F(0))
        require(total==1/a-1/(a+m*delta),'exact precision-kernel telescoping')
        kernel_count+=1
    for count in [2,3,8,17]:
        r=[F(2*i+1,4*count) for i in range(count)]
        decreasing=[4/(1+x) for x in r]
        increasing=[1/(1-x)**2 for x in r]
        require(count*sum((x*y for x,y in zip(decreasing,increasing)),F(0))
                <=sum(decreasing,F(0))*sum(increasing,F(0)),
                'oppositely monotone weighted prediction comparison')
    entropy_lower=1+F(109,128)
    prediction_upper=F(15625,4096)*F(5,12)+F(5,12288)
    gap=entropy_lower-prediction_upper
    require(gap==F(12863,49152) and gap>0,'finite rigorous nonconvex unweighted counterexample')
    limiting_ratios=[]
    with localcontext() as context:
        context.prec=60
        for integer in [1,2,10,100,1000,10000]:
            t=Decimal(integer); z=Decimal('0.5')
            logpart=(1+z/t).ln()
            numerator=logpart-(1-z).ln()+z*(1+t)/(1-z)
            denominator=(1+t)**2*logpart
            limiting_ratios.append({'t':integer,'R_infinity_ratio':str(numerator/denominator)})
    print(json.dumps({
        'status':'PASS',
        'arithmetic':'fractions.Fraction for exact checks; Decimal(60) for illustrative limiting ratios',
        'Gaussian_cubic_prediction_cases':prediction_count,
        'weighted_limit_derivative_cases':derivative_count,
        'adaptive_nested_minimum_cases':minimum_count,
        'finite_states_per_minimum_case':64,
        'precision_kernel_telescope_cases':kernel_count,
        'monotone_comparison_cases':4,
        'rigorous_finite_unweighted_counterexample_gap':str(gap),
        'illustrative_sharpness_ratios_not_interval_certificates':limiting_ratios,
        'scope':'Finite algebra and explicit analytic counterexample certificate. Universal analytic proof is entropy.tex.'
    },indent=2,sort_keys=True))

if __name__=='__main__':
    main()
