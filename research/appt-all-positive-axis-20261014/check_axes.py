#!/usr/bin/env python3
"""Exact endpoint/chord controls and finite actual APPT-family diagnostics."""
from argparse import ArgumentParser
from decimal import Decimal as D, localcontext, ROUND_FLOOR
from fractions import Fraction as F
from pathlib import Path
import json

def exact_controls():
    chord=[]; bulk2=[]; negative=[]
    for m in (3,4,5,8,12):
        q=F(m+1,m-1); t=q-1; theta2=1/(q+1)
        value=(1+theta2*(q*q-1))/(1+t*theta2)**2
        if value!=F(m*m,m*m-1):
            raise RuntimeError('Known scalar purity specialization failed')
        bulk2.append({'m':m,'exact_bulk_F2':str(value),'actual_finite_maximum_claim':False})
        for theta in (F(0),F(1,4),F(1,2),F(1)):
            mean=1+t*theta
            for j in range(5):
                z=1+t*F(j,4); low=(q-z)/t; high=(z-1)/t
                for alpha in (2,3):
                    phi=lambda x:(x**alpha-x)/(alpha-1)
                    gap=low*phi(1/mean)+high*phi(q/mean)-phi(z/mean)
                    expected=(z-1)*(q-z)/mean**2 if alpha==2 else (z-1)*(q-z)*(1+q+z)/(2*mean**3)
                    if gap!=expected or gap<0:
                        raise RuntimeError('Convex normalized chord identity failed')
                    chord.append({'m':m,'theta':str(theta),'z':str(z),'alpha':alpha,'exact_gap':str(gap)})
        for n in (m,m+1):
            dimension=m*n
            identity=[[F(i==j) for j in range(4)] for i in range(4)]
            p11=[[F(i==0 and j==0) for j in range(4)] for i in range(4)]
            plus=[[F(0) for _ in range(4)] for _ in range(4)]
            minus=[[F(0) for _ in range(4)] for _ in range(4)]
            for i in (1,2):
                for j in (1,2):
                    plus[i][j]=F(1,2); minus[i][j]=F(1,2) if i==j else F(-1,2)
            for projector in (p11,plus,minus):
                square=[[sum(projector[i][k]*projector[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
                if square!=projector or sum(projector[i][i] for i in range(4))!=1:
                    raise RuntimeError('Rank-one projector control failed')
            for kind,projector,sign,denominator,rank in (
                    ('rank_D_minus2',plus,-1,dimension-2,dimension-2),
                    ('nonflat_rank_D_minus1',minus,1,dimension,dimension-1)):
                block=[[(identity[i][j]-p11[i][j]+sign*projector[i][j])/denominator for j in range(4)] for i in range(4)]
                if sum(block[i][i] for i in range(4))+F(dimension-4,denominator)!=1:
                    raise RuntimeError('Embedded actual density trace failed')
                pt=[[F(0) for _ in range(4)] for _ in range(4)]
                for i in range(2):
                    for j in range(2):
                        for k in range(2):
                            for l in range(2):
                                pt[2*i+j][2*k+l]=block[2*i+l][2*k+j]
                vector=(F(4,5),F(0),F(0),F(3,5))
                expectation=sum(vector[i]*pt[i][j]*vector[j] for i in range(4) for j in range(4))
                if expectation!=F(-3,25*denominator):
                    raise RuntimeError('Actual endpoint negative PT control failed')
                negative.append({'m':m,'n':n,'D':dimension,'kind':kind,'actual_PSD_rank':rank,
                                 'unit_Schmidt_coefficients':['4/5','3/5'],'exact_PT_expectation':str(expectation),
                                 'APPT':False,'construction':'Identity minus/plus explicitly orthogonal rank-one projectors; outside block identity'})
    return chord,bulk2,negative

def dec(x):
    return D(x.numerator)/D(x.denominator) if isinstance(x,F) else D(x)

def bulk(alpha,q):
    t=q-1; lnq=q.ln()
    if alpha is None:
        return lnq,None
    if alpha==0:
        return D(0),1/lnq-1/t
    if alpha==1:
        z=q*lnq/t
        return z-1-z.ln(),(q*lnq-t)/(t*t)
    Q=(alpha*lnq).exp()
    theta=(Q-1-alpha*t)/(t*(alpha-1)*(Q-1))
    def g(x):
        return ((1+x*(Q-1)).ln()-alpha*(1+t*x).ln())/(alpha-1)
    value=g(theta)
    if not 0<theta<1 or any(g(D(j)/8)>value+D('1e-140') for j in range(9)):
        raise RuntimeError('Finite full-positive scalar optimization control failed')
    return value,theta

def entropy(groups,dimension,alpha):
    active=[(count,val) for count,val in groups if count>0]
    if sum(count*val for count,val in active)!=1 or any(val<0 for _,val in active):
        raise RuntimeError('Actual mixture lost its rational trace/PSD construction')
    values=[(count,dec(dimension*val)) for count,val in active]
    if alpha is None:
        return max(y for _,y in values).ln(),D(0)
    if alpha==0:
        rank=sum(count for count,val in active if val>0)
        return (D(dimension)/D(rank)).ln(),D(0)
    if alpha==1:
        result=sum(D(count)*y*y.ln() for count,y in values if y>0)/dimension
        return result,D(0)
    moment=sum(D(count)*(alpha*y.ln()).exp() for count,y in values if y>0)/dimension
    defect=sum(D(count)*((alpha*y.ln()).exp()-y)/(alpha-1) for count,y in values if y>0)/dimension
    direct=moment.ln()/(alpha-1)
    via_defect=(1+(alpha-1)*defect).ln()/(alpha-1)
    disagreement=abs(direct-via_defect)
    if disagreement>D('1e-140'):
        raise RuntimeError('Stable normalized defect/direct entropy correspondence failed')
    return direct,disagreement

def groups_for(dimension,m,rank,weights):
    q=F(m+1,m-1); t=q-1
    pole,projection,missing=weights
    if not 1<=rank<dimension or sum(weights)!=1 or any(w<0 for w in weights):
        raise RuntimeError('Illegal projection rank or mixture coefficients')
    high=q/(dimension+t*rank); low=1/(dimension+t*rank)
    first=pole*F(3,dimension+2)+projection*high+missing*F(1,dimension-1)
    other_high=pole*F(1,dimension+2)+projection*high+missing*F(1,dimension-1)
    other_low=pole*F(1,dimension+2)+projection*low+missing*F(1,dimension-1)
    last=pole*F(1,dimension+2)+projection*low
    return [(1,first),(rank-1,other_high),(dimension-rank-1,other_low),(1,last)]

def finite_controls():
    cases=[]; continuity=[]
    weights=((F(1),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1)),
             (F(1,3),F(1,3),F(1,3)),(F(1,2),F(1,2),F(0)),(F(0),F(1,2),F(1,2)))
    for m in (3,4,5,8,12):
        q=D(m+1)/D(m-1); t=q-1
        kappa=1/(D(3)/q).ln(); epsilon=1/(2*D(3).ln())
        at_one,_=bulk(D(1),q)
        for alpha in (D(1)-D('1e-90'),D(1)+D('1e-90')):
            value,_=bulk(alpha,q)
            if abs(value-at_one)>D('1e-80'):
                raise RuntimeError('Cross-one finite continuity control failed')
            continuity.append({'m':m,'alpha':str(alpha),'bulk_minus_vonNeumann':str(value-at_one)})
        for exponent in (1,2,6):
            n=m*10**exponent; dimension=m*n; L=D(dimension).ln()
            X=kappa*(L-L.ln()-(D(1).exp()*t*kappa).ln())
            orders=[('zero',D(0)),('tiny',D('1e-90')),('small',D('1e-40')),
                    ('quarter',D('0.25')),('half',D('0.5')),('below1',D('0.9')),
                    ('one_minus_tiny',D(1)-D('1e-90')),('one',D(1)),
                    ('one_plus_tiny',D(1)+D('1e-90')),('above1',D('1.1')),
                    ('two',D(2)),('three',D(3)),('epsilon_logD',epsilon*L),
                    ('kappa_logD',kappa*L),('critical_X',X),
                    ('high_band_start',(kappa+1)*L+1),('very_high',100*L),('infinity',None)]
            for label,alpha in orders:
                model,theta=bulk(alpha,q)
                if theta is None:
                    rank=1
                else:
                    rank=int((D(dimension)*theta).to_integral_value(rounding=ROUND_FLOOR))
                    rank=max(1,min(dimension-1,rank))
                pole_deficit,_=entropy(groups_for(dimension,m,rank,weights[0]),dimension,alpha)
                missing_deficit=(D(dimension)/D(dimension-1)).ln()
                composite=max(model,pole_deficit)
                all_family_bound=max(composite,missing_deficit)
                rows=[]
                for mix in weights:
                    value,correspondence=entropy(groups_for(dimension,m,rank,mix),dimension,alpha)
                    if value>all_family_bound+D('1e-135'):
                        raise RuntimeError('Finite actual three-family convex-mixture control failed')
                    rows.append({'weights':[str(w) for w in mix],'entropy_deficit':str(value),
                                 'minus_composite_model':str(value-composite),
                                 'Tsallis_direct_disagreement':str(correspondence)})
                cases.append({'m':m,'n':n,'D':dimension,'order_label':label,
                              'alpha':'infinity' if alpha is None else str(alpha),
                              'actual_projection_rank':rank,'bulk_model':str(model),
                              'pole_deficit':str(pole_deficit),'missing_projector_deficit':str(missing_deficit),
                              'actual_APPT_mixtures':rows})
    return cases,continuity

def main():
    parser=ArgumentParser(); parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    chord,bulk2,negative=exact_controls()
    with localcontext() as ctx:
        ctx.prec=260
        cases,continuity=finite_controls()
    result={'status':'PASS','kind':'Exact finite controls and finite actual-family diagnostics; not all-set or all-order proof',
            'decimal_precision':260,'normalized_chord_controls':chord,'known_scalar_purity_controls':bulk2,
            'actual_PSD_nonAPPT_rank_controls':negative,'cross_one_continuity_controls':continuity,
            'actual_dimension_order_cases':cases,'mixture_APPT_basis':'Convex combinations of credited pole, actual projection and missing-projector APPT families',
            'implementations':1,'global_APPT_set_exhausted_by_checks':False,
            'finite_dimension_threshold_certified':False,'new_Lean_execution':False,'new_audit_roots':0}
    args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','exact_chord_controls':len(chord),'known_scalar_purity_controls':len(bulk2),
                     'actual_endpoint_negative_controls':len(negative),'cross_one_controls':len(continuity),
                     'actual_dimension_order_cases':len(cases),
                     'actual_mixture_evaluations':sum(len(c['actual_APPT_mixtures']) for c in cases),'out':str(args.out)}))

if __name__=='__main__':
    main()
