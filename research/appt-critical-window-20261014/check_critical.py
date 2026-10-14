#!/usr/bin/env python3
"""Finite exact pivot controls and numerical window diagnostics, not proofs."""
from argparse import ArgumentParser
from decimal import Decimal, localcontext
from fractions import Fraction as F
from pathlib import Path
import json


def require(value,message):
    if not value:
        raise RuntimeError(message)


def dec(x):
    return Decimal(x.numerator)/Decimal(x.denominator)


def exact_scalar():
    cases=points=0
    for ell in (3,4,5,8,12):
        R=ell*(ell-1)//2; K=ell*(ell+1)//2; q=F(K,R); t=q-1
        require(R+K==ell**2 and t*R==ell, 'fixed Schmidt sector counts')
        for alpha in (2,3,4,8,16):
            Q=q**alpha
            theta=(Q-1-alpha*t)/(t*(alpha-1)*(Q-1))
            require(0<theta<1, 'exact interior chord maximum')
            formula=F((alpha-1)**(alpha-1),alpha**alpha)*(Q-1)**alpha/(t*(Q-q)**(alpha-1))
            value=(1+theta*(Q-1))/(1+t*theta)**alpha
            require(value==formula, 'exact scalar closed formula')
            require(Q-1-alpha*t-t*(alpha-1)*(Q-1)*theta==0, 'exact scalar stationary identity')
            for s in (F(0),F(1,5),F(1,2),F(4,5),F(1),theta):
                require((1+s*(Q-1))/(1+t*s)**alpha<=formula, 'finite rational chord comparison')
                points+=1
            cases+=1
    return {'exact_integer_order_scalar_cases':cases,'finite_rational_comparisons':points,
            'universal_real_order_proof_not_inferred':True}


def actual_pivot_controls():
    rows=[]
    for m,n in ((3,4),(3,5),(4,4)):
        d=m*n; matrix=[[F(0) for _ in range(d)] for _ in range(d)]
        for a in range(m):
            for b in range(n):
                matrix[a*n+b][a*n+b]=F(1) if a<3 and b<3 else F(11,10)
        for (a,b),weight in (((0,1),F(3,2)),((0,2),F(7,5)),((1,2),F(1,10))):
            i,j=a*n+b,b*n+a
            matrix[i][i]+=weight/2; matrix[j][j]+=weight/2
            matrix[i][j]-=weight/2; matrix[j][i]-=weight/2
        Z=sum(matrix[i][i] for i in range(d))
        require(Z==F(11*d+21,10), 'actual positive density normalization')
        spectrum=[F(5,2),F(12,5)]+[F(11,10)]*(d-8)+[F(1)]*6
        require(sum(spectrum)==Z and spectrum==sorted(spectrum,reverse=True), 'actual projector spectrum')
        require(sum(spectrum[:3])==sum(spectrum[-6:])==6, 'top R and bottom K inequality passes')
        require(spectrum[0]<=3 and spectrum[1]/Z<=F(5,2*(d+3)), 'old rank-two and second cap pass')
        beta=(Z-spectrum[0]-spectrum[1])/(d-2)
        require((spectrum[0]-beta)**2+(spectrum[1]-beta)**2<=4*beta**2,
                'old averaged two-head circle passes')
        require((spectrum[0]-1)**2+(spectrum[1]-1)**2==F(421,100)>4,
                'new common-pivot circle fails')
        w=[F(0)]*d
        for a,value in enumerate((F(36,49),F(24,49),F(23,49))):
            w[a*n+a]=value
        require(sum(x*x for x in w)==1, 'actual rational Schmidt unit test')
        expectation=F(0)
        for i in range(d):
            a,b=divmod(i,n)
            for j in range(d):
                c,e=divmod(j,n)
                expectation+=w[i]*matrix[a*n+e][c*n+b]*w[j]/Z
        require(expectation==-F(547,12005)/Z, 'exact actual common-pivot PPT negative control')
        rows.append({'pair':[m,n],'positive_density_from_nonnegative_orthogonal_projectors':True,
            'trace_normalizer':str(Z),'old_outer_second_cap_and_averaged_circle_pass':True,
            'top3_bottom6_pass':True,'common_pivot_circle':'421/100>4',
            'partial_transpose_expectation':str(expectation),'not_APPT':True})
    return rows


def chord_max(q,alpha):
    Q=(alpha*q.ln()).exp(); t=q-1
    theta=(Q-1-alpha*t)/(t*(alpha-1)*(Q-1))
    require(0<theta<1, 'numerical scalar interior')
    return (1+theta*(Q-1))/((alpha*(1+t*theta).ln()).exp())


def window_diagnostics():
    rows=[]
    for ell in (3,4,5,8,12):
        q=Decimal(ell+1)/Decimal(ell-1); t=q-1; kappa=1/(3/q).ln()
        R=ell*(ell-1)//2; K=ell*(ell+1)//2; H=R-1
        h=t*t/256; W=1+t/4; L=3-2*h
        eta=t*t/16; qeta=1+(4*eta-eta*eta).sqrt()
        require(W<q and L/W>3/q and 1<qeta<q, 'valid full-range split constants')
        for exponent in (20,100,1000,4000):
            d=ell*10**exponent; D=Decimal(d); logD=D.ln(); loglogD=logD.ln()
            center=kappa*(logD-loglogD); sstar=-kappa*(t*kappa).ln()-kappa
            X=center+sstar; u=3*D/(D+2); L0=D-H-K; L1=D-K-1
            for offset in (Decimal(-2),Decimal('-0.25'),Decimal(0),Decimal('0.25'),Decimal(2)):
                alpha=X+offset; T=alpha-1; rank=int(D/(t*alpha)); theta=Decimal(rank)/D
                require(1<=rank<d and alpha>2, 'actual projection rank at finite critical order')
                projection=(1-theta+theta*(alpha*q.ln()).exp())/((alpha*(1+t*theta).ln()).exp())
                pole=((alpha*Decimal(3).ln()).exp()+D-1)/D*(alpha*(D/(D+2)).ln()).exp()
                Fq=chord_max(q,alpha); Feta=chord_max(qeta,alpha)
                require(projection<=Fq*(1+Decimal('1e-130')), 'actual family against exact scalar maximum')
                near=(T*(L/W).ln()).exp()/(1+T*(D-1))
                far=(alpha*(D/L0).ln()).exp()*(H*(alpha*(3-eta).ln()).exp()+K)/D
                far+=(T*(D/L0).ln()).exp()*Fq
                other=((alpha*(u-h).ln()).exp())/D+(T*(D/L1).ln()).exp()*Feta
                other+=(alpha*(D/L1).ln()).exp()*K/D
                ratio=projection/pole; limit=(-offset/kappa).exp()
                B=((kappa*q.ln()*logD)-(kappa*Decimal(3).ln()*loglogD)).exp()
                predicted=max(((sstar+offset)*Decimal(3).ln()).exp(),
                              ((sstar+offset)*q.ln()).exp()/(t*kappa*Decimal(1).exp()))
                lower=max(projection,pole)/B
                if exponent==4000:
                    require(abs(ratio/limit-1)<Decimal('0.01'), 'finite bulk/pole constant-offset diagnostic')
                    require(abs(lower/predicted-1)<Decimal('0.01'), 'finite moment-envelope diagnostic')
                    require(near>1 and other<pole, 'large finite near/other-branch bound diagnostic')
                    if offset<0:
                        require(ratio>1, 'actual finite subcritical APPT competitor')
                    elif offset>0:
                        require(far<pole, 'large finite far-branch scalar diagnostic')
                rows.append({'ell':ell,'D_expression':str(ell)+'*10^'+str(exponent),
                    'alpha':str(alpha),'offset_from_X':str(offset),'projection_rank_bits':rank.bit_length(),
                    'bulk_pole_ratio':str(ratio),'predicted_ratio_limit':str(limit),
                    'lower_moment_scaled':str(lower),'predicted_envelope':str(predicted),
                    'near_cap_scalar_ratio':str(near),'far_upper_over_pole':str(far/pole),
                    'relative_near_peak_far_cap_upper_over_pole':str(other/pole),
                    'finite_diagnostics_only':True,'projection_APPT_only':True})
    return rows


def main():
    parser=ArgumentParser(); parser.add_argument('--out',type=Path); args=parser.parse_args()
    with localcontext() as ctx:
        ctx.prec=150
        record={'status':'PASS','kind':'finite exact physical controls and finite numerical diagnostics',
                'universal_proof':'PAPER.md, not evaluated cases','implementation_count':1,
                'precision_digits':ctx.prec,'scalar':exact_scalar(),
                'actual_pivot_controls':actual_pivot_controls(),'window_diagnostics':window_diagnostics(),
                'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','exact_scalar_cases':record['scalar']['exact_integer_order_scalar_cases'],
        'finite_rational_comparisons':record['scalar']['finite_rational_comparisons'],
        'actual_common_pivot_PPT_negative_controls':len(record['actual_pivot_controls']),
        'finite_critical_window_cases':len(record['window_diagnostics']),
        'implementation_count':1,'universal_proof_not_inferred':True}))


if __name__=='__main__':
    main()
