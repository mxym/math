#!/usr/bin/env python3
"""Finite exact controls and scalar diagnostics; PAPER.md proves full ranges."""
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


def exact_controls():
    dimensions=[]
    for ell in (3,4,5,6,8,12):
        r=ell*(ell-1)//2; q=F(ell+1,ell-1); t=q-1
        for n in (ell,ell+1,2*ell):
            d=ell*n; a=q/(d+ell); b=F(1,d+ell)
            require(t*r==ell and r*a+(d-r)*b==1, 'finite-head cap normalization')
            require(b-F(ell-1,2)*(a-b)==0, 'actual maximally entangled negative-subspace test')
            require(F(d,d-1)<q and r<d, 'Taylor center and head count')
            epsilon=F(1,100*(d+ell)); a+=epsilon; b=(1-r*a)/(d-r)
            expectation=b-F(ell-1,2)*(a-b)
            require(b>0 and expectation<0, 'actual density above cap has negative PPT expectation')
            dimensions.append({'ell':ell,'n':n,'D':d,'negative_rank':r,
                'above_cap_density_PPT_expectation':str(expectation),
                'cap_necessary_only':True})
    algebra=0
    for d in (9,12,16,21,30,64,128):
        b0=F(d,d+2); u=3*b0
        for denominator in (20,100,10000):
            delta=u/denominator; p=u-delta; mu=(d-p)/(d-1)
            for factor in (F(1,d-1),F(1,2),F(1),F(3)):
                z=factor*delta; s=b0+z; beta=(d-p-s)/(d-2)
                require(3*beta-p==((d+1)*delta-3*z)/(d-2), 'exact two-head trace identity')
                require(s-mu==F(d-2,d-1)*(s-beta), 'exact tail mean identity')
                require(4*beta**2-(p-beta)**2==(3*beta-p)*(beta+p), 'circle factorization')
                algebra+=1
    # Genuine 3x3 spectrum (p,s,beta,...)/D passes the linear outer and
    # old second-eigenvalue cap but an actual rational PPT test is negative.
    d=9; p,s,beta=F(9,4),F(3,2),F(3,4)
    require(p+s+7*beta==d and p==3*beta and s/d<=F(5,2*(d+3)), 'false-relaxation density checks')
    value=(beta-F(4,9)*(p-beta)-F(2,9)*(s-beta))/d
    require(value==F(-1,108), 'actual two-head PPT negative control')
    require(F(165,28)<6, 'dimension-free exceptional variance constant')
    return {'physical_cap_controls':dimensions,'exact_two_head_identity_points':algebra,
            'identity_points_not_asserted_APPT':True,
            'actual_3x3_circle_control':{'scaled_spectrum':['9/4','3/2']+['3/4']*7,
                'normalizer':9,'Schmidt_vector':['2/3','2/3','1/3'],
                'negative_partial_transpose_expectation':str(value),
                'linear_outer_and_old_second_cap_pass':True,'not_APPT':True}}


def band_diagnostics():
    rows=[]
    for ell in (3,4,5,8):
        r=ell*(ell-1)//2; q=Decimal(ell+1)/Decimal(ell-1)
        kappa=1/(3/q).ln(); V=Decimal('2.5')
        for multiplier in (Decimal('1.1'),Decimal('1.5'),Decimal(2)):
            c=multiplier*kappa
            epsilon=(3-max(V,q*(1/c).exp()))/4; L=3-2*epsilon
            require(L>V and c*(L/q).ln()>1, 'strict choice of continuous comparison constants')
            for exponent in (10,50,200,1000):
                d=ell*10**exponent; D=Decimal(d); u=3*D/(D+2)
                T0=c*D.ln(); last=None
                for scale in (Decimal(1),Decimal('1.01'),Decimal(2)):
                    T=T0*scale; alpha=T+1
                    near=(1+5*T*(D-1)/(2*q))*(T*(q/L).ln()).exp()
                    near+=6*T*(r-2)/5*(T*(V/L).ln()).exp()
                    far=(r-1)*(alpha*(1-epsilon/3).ln()).exp()+D*(alpha*(q/(3-epsilon)).ln()).exp()
                    if last is not None:
                        require(near<last[0] and far<last[1], 'finite whole-order monotonicity diagnostic')
                    last=(near,far)
                    if exponent==1000:
                        require(near<1 and far<1, 'large-D near/far scalar diagnostic')
                    rows.append({'ell':ell,'D':str(d),'c_over_kappa':str(multiplier),'T_scale':str(scale),
                        'near_ratio':str(near),'far_ratio':str(far),
                        'both_strict_below1':near<1 and far<1})
    return rows


def phase_diagnostics():
    rows=[]
    for m in (3,4,5,8):
        r=m*(m-1)//2; q=Decimal(m+1)/Decimal(m-1); t=q-1
        kappa=1/(3/q).ln()
        for exponent in (8,30,100):
            d=m*10**exponent; D=Decimal(d); logD=D.ln(); u=3*D/(D+2)
            choices=[('c0',logD.sqrt()),('subcritical',kappa*logD/2),
                     ('critical',kappa*logD),('supercritical',2*kappa*logD),('cinfinity',logD**2)]
            for label,alpha in choices:
                rank=int(D/(t*alpha)); theta=Decimal(rank)/D
                require(1<=rank<d and alpha>1, 'genuine actual projection family')
                projection=(1-theta+theta*(alpha*q.ln()).exp())/((alpha*(1+t*theta).ln()).exp())
                pole=((alpha*Decimal(3).ln()).exp()+D-1)/D*(alpha*(D/(D+2)).ln()).exp()
                upper=(r-1)/D*(alpha*u.ln()).exp()+(D-r+1)/D*(alpha*(q*D/(D+m)).ln()).exp()
                lower=max(projection,pole)
                require(lower<=upper*(1+Decimal('1e-80')), 'actual lower families against necessary upper cap')
                rows.append({'m':m,'D':str(d),'regime':label,'alpha':str(alpha),
                    'physical_lower_entropy_deficit':str(lower.ln()/(alpha-1)),
                    'necessary_upper_entropy_deficit':str(upper.ln()/(alpha-1)),
                    'finite_c_expression':str(max(q.ln(),Decimal(3).ln()-logD/alpha)),
                    'projection_APPT_only':True})
    return rows


def main():
    parser=ArgumentParser(); parser.add_argument('--out',type=Path); args=parser.parse_args()
    with localcontext() as ctx:
        ctx.prec=110
        record={'status':'PASS','kind':'finite exact controls and finite numerical diagnostics',
                'universal_proof':'PAPER.md, not these diagnostics','implementation_count':1,
                'precision_digits':ctx.prec,'exact':exact_controls(),
                'band_diagnostics':band_diagnostics(),'phase_diagnostics':phase_diagnostics(),
                'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','physical_cap_controls':len(record['exact']['physical_cap_controls']),
        'exact_two_head_identity_points':record['exact']['exact_two_head_identity_points'],
        'actual_circle_negative_control':'3x3, expectation -1/108',
        'finite_real_order_band_cases':len(record['band_diagnostics']),
        'finite_fixed_local_phase_cases':len(record['phase_diagnostics']),
        'implementation_count':1,'universal_proof_not_inferred':True}))


if __name__=='__main__':
    main()
