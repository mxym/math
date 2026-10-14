#!/usr/bin/env python3
"""Exact coefficient controls and finite decimal diagnostics, never a proof."""
from argparse import ArgumentParser
from decimal import Decimal as D, localcontext, ROUND_FLOOR
from fractions import Fraction as F
from pathlib import Path
import json

def exact_controls():
    expansions=[]
    for a in (F(3,5),F(1),F(2)):
        for U in (F(-2),F(0),F(2),F(5)):
            d1=U+a/2
            d2=U*U/2+(a/2-1)*U+a*a/6-a/2
            r1=d1-U-a/2
            r2=d2+d1-U*U/2-a*U/2-a*a/6
            if r1 or r2:
                raise RuntimeError('Inverse-log coefficient identity failed')
            expansions.append({'a':str(a),'U':str(U),'coeff_L_minus1':str(r1),'coeff_L_minus2':str(r2)})
    derivative=[]
    for x in (F(3,2),F(2),F(3),F(8),F(16)):
        value=1/x-(x-1)/(x*(x-1))
        if value:
            raise RuntimeError('Model derivative cancellation failed')
        derivative.append({'alpha':str(x),'exact_cancelled_terms':str(value)})
    return expansions,derivative

def finite_case(m,exponent):
    q=D(m+1)/D(m-1); t=q-1
    a=(D(3)/q).ln(); kappa=1/a
    lnq=q.ln(); ln3=D(3).ln()
    n_int=10**exponent; dimension=m*n_int; dimension_dec=D(dimension)
    L=dimension_dec.ln(); b=(D(1).exp()*t*kappa).ln(); U=L.ln()+b
    X=kappa*(L-U); ln_b0=(dimension_dec/(dimension_dec+2)).ln()
    h=t*t/256; eta=t*t/16; v=1+(4*eta-eta*eta).sqrt()
    beta=min(D(1),kappa*lnq,kappa*(D(3)/(3-eta)).ln(),
             kappa*(1/(1-h/3)).ln(),kappa*(D(3)/v).ln()-1)/4
    if beta<=0:
        raise RuntimeError('Sufficient exponent is not positive')
    tolerance=D('1e-185')
    def model(x):
        logpart=(1-1/x).ln()
        return a*x+(t*x).ln()-(x-1)*logpart-L, a-logpart
    def scalar(x):
        inverseQ=(-x*lnq).exp()
        theta=(1-(1+x*t)*inverseQ)/(t*(x-1)*(1-inverseQ))
        logF=x*lnq-(t*x).ln()+(x-1)*(1-1/x).ln()
        correction=x*(1-inverseQ).ln()-(x-1)*(1-q*inverseQ).ln()
        logF+=correction
        extra=(dimension_dec-1)*(-x*ln3).exp()
        logP=x*ln3-L+x*ln_b0+(1+extra).ln()
        residual=-model(x)[0]+correction-x*ln_b0-(1+extra).ln()
        logF_derivative=theta/(inverseQ+theta*(1-inverseQ))*lnq-(1+t*theta).ln()
        derivative=logF_derivative-ln_b0-ln3/(1+extra)
        direct=x*lnq+(theta+(1-theta)*inverseQ).ln()-x*(1+t*theta).ln()
        if abs(logF-direct)>tolerance:
            raise RuntimeError('Independent chord value correspondence failed')
        return residual,derivative,theta,logF,logP,inverseQ
    def newton(fn,start):
        x=start
        for _ in range(12):
            value,derivative=fn(x)[:2]
            if abs(value)<=tolerance:
                return x
            x-=value/derivative
            if x<=1:
                raise RuntimeError('Newton left the declared root domain')
        if abs(fn(x)[0])>tolerance:
            raise RuntimeError('Root residual exceeds finite working tolerance')
        return x
    elementary=newton(model,X)
    crossing=newton(scalar,elementary)
    lambert=newton(lambda x:(a*x+(t*x).ln()+1-L,a+1/x),X)
    first=kappa*(L-U)+(kappa*U+D(1)/2)/L
    second=first+(kappa*U*U/2+(D(1)/2-kappa)*U+1/(6*kappa)-D(1)/2)/(L*L)
    points=[]
    epsilon=(-beta*L).exp()
    for offset in (-2,0,2):
        x=crossing+D(offset)
        residual,derivative,theta,logF,logP,inverseQ=scalar(x)
        slope_margin_observed=derivative<=-a/2+tolerance
        # The theorem is eventual: retain smaller-D failures instead of
        # treating the smallest finite sample as a certified threshold.
        if exponent==160 and not slope_margin_observed:
            raise RuntimeError('Largest sampled higher-order slope control failed: '+str((m,exponent,offset)))
        rank=int((dimension_dec*theta).to_integral_value(rounding=ROUND_FLOOR))
        rounded=D(rank)/dimension_dec
        if not 1<=rank<dimension or not 0<=theta-rounded<=1/dimension_dec:
            raise RuntimeError('Illegal actual integer-rank state or rounding')
        actual=x*lnq+(rounded+(1-rounded)*inverseQ).ln()-x*(1+t*rounded).ln()
        loss=logF-actual
        bound=100*(1+t*t)*x*x/(dimension_dec*dimension_dec)
        if loss < -tolerance or loss>bound+tolerance:
            raise RuntimeError('Finite rank-rounding moment loss exceeds control')
        points.append({'offset_from_crossing':offset,'log_ratio':str(residual),
                       'log_ratio_derivative':str(derivative),'eventual_slope_margin_observed':slope_margin_observed,
                       'actual_rank_bits':rank.bit_length(),
                       'continuous_minus_integer_log_moment':str(loss),
                       'loss_resolution_note':'Values below220-digit working resolution may round to zero; zero is not asserted exact.'})
    x=crossing-epsilon
    residual,derivative,theta,logF,logP,inverseQ=scalar(x)
    rank=int((dimension_dec*theta).to_integral_value(rounding=ROUND_FLOOR))
    rounded=D(rank)/dimension_dec
    actual=x*lnq+(rounded+(1-rounded)*inverseQ).ln()-x*(1+t*rounded).ln()
    lower_log_ratio=actual-logP
    if not 1<=rank<dimension or lower_log_ratio<=0:
        raise RuntimeError('Actual projection lower-control state failed')
    return {'m':m,'n_expression':'10^'+str(exponent),'D_expression':str(m)+'*10^'+str(exponent),
            'beta_sufficient':str(beta),'exact_scalar_crossing_decimal':str(crossing),
            'elementary_model_root_decimal':str(elementary),
            'scalar_minus_model':str(crossing-elementary),
            'model_minus_two_correction_formula':str(elementary-second),
            'scaled_two_correction_remainder':str((elementary-second)*L**3/(1+abs(U)**3)),
            'model_minus_Lambert_root':str(elementary-lambert),
            'scaled_Lambert_difference':str((elementary-lambert)*L),
            'actual_APPT_lower_order':str(x),'actual_APPT_lower_log_moment_ratio':str(lower_log_ratio),
            'higher_order_and_rounding_points':points}

def main():
    parser=ArgumentParser(); parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    expansions,derivative=exact_controls()
    with localcontext() as ctx:
        ctx.prec=220
        cases=[finite_case(m,exponent) for m in (3,4,5,8,12) for exponent in (12,32,64,100,160)]
    result={'status':'PASS','kind':'Exact finite identities and finite high-precision diagnostics, not an all-domain proof',
            'decimal_precision':220,'exact_expansion_controls':expansions,
            'exact_derivative_cancellations':derivative,'actual_fixed_local_cases':cases,
            'actual_dimensions':'m-by-10^exponent; D is not an inadmissible rounded dimension',
            'implementations':1,'new_Lean_execution':False,'new_audit_roots':0,
            'finite_threshold_certified':False,'exact_finite_optimizer_classification':False,
            'smaller_sample_slope_margin_failures':sum(not p['eventual_slope_margin_observed'] for c in cases for p in c['higher_order_and_rounding_points'])}
    args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','expansion_identity_controls':len(expansions),
                     'derivative_exact_controls':len(derivative),'actual_dimension_cases':len(cases),
                     'real_order_slope_and_rank_points':sum(len(c['higher_order_and_rounding_points']) for c in cases),
                     'smaller_sample_slope_margin_failures':result['smaller_sample_slope_margin_failures'],
                     'out':str(args.out)}))

if __name__=='__main__':
    main()
