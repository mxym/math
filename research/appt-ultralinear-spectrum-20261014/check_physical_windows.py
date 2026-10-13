"""Finite physical-family diagnostics, not a proof of APPT optimization.

Every state is specified by exact rational strength/protection, integer
projection rank and exact trace normalization. Its universal APPT property
is the cited written Schmidt proof, not a sampled-unitary numerical test.
Moments below are high-precision evaluations of its finite multiplicities.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
import math
import platform
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def dec(value):
    if isinstance(value, Fraction):
        return Decimal(value.numerator)/Decimal(value.denominator)
    return Decimal(value)

def logsum(terms):
    top = max(terms)
    return top+sum((x-top).exp() for x in terms if x-top > -180).ln()

def bulk(m, alpha, strength=None):
    k = Fraction(2, m-1) if strength is None else strength
    kd = dec(k)
    a = Decimal(alpha)
    z = (a*(1+kd).ln()).exp()-1
    q = (z-a*kd)/(kd*z*(a-1))
    require(0<q<1, 'Bulk mixing fraction not interior')
    logb = (z/(a*kd)).ln()+(1-a)*(a/(a-1)*(1-kd/z)).ln()
    return q, logb

def dimension(m, alpha, logb, log_ratio):
    logd = Decimal(alpha)*Decimal(3).ln()-logb-Decimal(str(log_ratio))
    target = logd.exp()
    n = max(m, int(target/Decimal(m)+Decimal('0.5')))
    return m*n

def physical_moment(m, alpha, dsize, strength, fraction, protected):
    k = strength
    if protected:
        den = 2-(m-3)*k
        d = (2-(m-1)*k)*(2+k)/den
        require(d>=0 and den>0, 'Invalid exact protection coefficient')
    else:
        d = Fraction(0)
    require(0<=k<=Fraction(2,m-1), 'Strength outside physical interval')
    f = Fraction(float(fraction))
    rank = max(1,min(dsize-1,f.numerator*dsize//f.denominator))
    trace = Fraction(dsize)+k*rank+d
    require(trace>0 and 1+k+d>0, 'Exact density positivity/trace failed')
    dd = Decimal(dsize); a = Decimal(alpha)
    norm = dec(trace)/dd
    high = dec(1+k+d); upper = dec(1+k)
    terms = [a*high.ln()-dd.ln()]
    if rank>1:
        terms.append((Decimal(rank-1)/dd).ln()+a*upper.ln())
    if dsize>rank:
        terms.append((Decimal(dsize-rank)/dd).ln())
    logm = logsum(terms)-a*norm.ln()
    return logm, rank

def scalar_scan(m, alpha, peak, grid=1200):
    a=float(alpha); cap=2/(m-1)
    best=(math.log1p(peak), 0, 0.0)
    for index in range(1,grid+1):
        k=cap*index/grid
        eta=2*(m-2)*k*k/(2-(m-3)*k)
        z=math.expm1(a*math.log1p(k))
        head=peak*math.exp(a*math.log1p(-eta/3))
        c0=1+head
        q=max(0.0,(z-a*k*c0)/(k*z*(a-1)))
        require(q<1, 'Scalar derivative produced out-of-range fraction')
        value=math.log(c0+q*z)-a*math.log1p(k*q)
        if value>best[0]:
            best=(value,index,q)
    return best

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--out')
    args=parser.parse_args()
    windows=[]; separation=[]; cap_controls=[]
    with localcontext() as context:
        context.prec=80
        # Thirty-six finite peak/bulk-window comparisons. A scan certifies
        # only the evaluated competitor, not the universal scalar maximum.
        for m in (20,80,200):
            for c in (2,5,10,30):
                alpha=m*c
                qb, logb=bulk(m,alpha)
                for shift in (-2,0,2):
                    dsize=dimension(m,alpha,logb,shift)
                    dd=Decimal(dsize)
                    u=3*dd/(dd+2)
                    logp=Decimal(alpha)*u.ln()-dd.ln()
                    benchmark=max(logb,logp)
                    logsp,_=physical_moment(m,alpha,dsize,Fraction(0),0.0,True)
                    logprojection,rank=physical_moment(m,alpha,dsize,Fraction(2,m-1),qb,False)
                    require(abs(logprojection-logb)<Decimal('1e-9'), 'Projection/rank window comparison failed')
                    scan_log,index,q=scalar_scan(m,alpha,float(logp.exp()))
                    strength=Fraction(2*index,(m-1)*1200)
                    actual,_=physical_moment(m,alpha,dsize,strength,q,True)
                    require(abs(float(actual)-scan_log)<1e-8, 'Actual protected spectrum differs from scanned scalar competitor')
                    windows.append({'m':m,'alpha':alpha,'alpha_over_m':c,
                                    'target_log_peak_over_bulk':shift,
                                    'actual_log_peak_over_bulk':float(logp-logb),
                                    'log_D':float(dd.ln()),
                                    'upper_rank_fraction':float(Decimal(rank)/dd),
                                    'bulk_scaled_mean':float(Decimal(alpha)*dec(Fraction(2,m-1))*Decimal(rank)/dd),
                                    'pure_spike_log_ratio_to_benchmark':float(logsp-benchmark),
                                    'projection_log_ratio_to_benchmark':float(logprojection-benchmark),
                                    'best_scanned_physical_log_ratio_to_benchmark':float(actual-benchmark),
                                    'scan_is_universal_maximum_certificate':False})
        # Exact rational projection strengths exhibit the weaker entropy
        # scale. These finite values supplement the analytic sequence proof.
        for m in (20,40,100,200):
            alpha=m*m
            qb,logb=bulk(m,alpha)
            dsize=dimension(m,alpha,logb,0)
            eps=Fraction(float(1/math.sqrt(m)))
            strength=(1-eps)*Fraction(2,m-1)
            q,logtarget=bulk(m,alpha,strength)
            actual,_=physical_moment(m,alpha,dsize,strength,q,False)
            require(abs(actual-logtarget)<Decimal('1e-9'), 'Separating physical projection moment failed')
            g=Decimal(alpha)*((1+dec(Fraction(2,m-1)))/(1+dec(strength))).ln()
            separation.append({'m':m,'alpha':alpha,'width_defect_G':float(g),
                               'moment_ratio_to_bulk_benchmark':float((actual-logb).exp()),
                               'entropy_deficit_ratio_to_bulk_benchmark':float(actual/logb),
                               'actual_rational_strength':str(strength)})
        # A wrong uncalibrated top base is visibly invalid when alpha>>D.
        for m in (20,80):
            dsize=m*m; alpha=dsize*dsize; dd=Decimal(dsize)
            u=3*dd/(dd+2)
            logp=Decimal(alpha)*u.ln()-dd.ln()
            actual,_=physical_moment(m,alpha,dsize,Fraction(0),0.0,True)
            wrong=Decimal(alpha)*Decimal(3).ln()-dd.ln()
            require(abs(actual-logp)<Decimal('1e-9'), 'Exact pure-spike peak calibration failed')
            require(wrong-actual>100, 'Uncalibrated-base negative control failed')
            cap_controls.append({'m':m,'D':dsize,'alpha':alpha,
                                 'actual_pure_spike_log_ratio_to_exact_peak':float(actual-logp),
                                 'wrong_base_log_overstatement':float(wrong-actual)})
    record={'kind':'Finite exact-parameter physical-family moment evaluations',
            'python_version':platform.python_version(),'optimized':not __debug__,
            'exact_state_parameters':'Rational strength/protection, integer rank, rational trace; numerical powers',
            'window_cases':windows,'entropy_vs_moment_cases':separation,
            'uncalibrated_base_negative_controls':cap_controls,
            'case_count':len(windows)+len(separation)+len(cap_controls),
            'universal_theorem_proved_by_diagnostics':False,
            'sampled_unitary_tests':False,'lean_execution':False,'status':'PASS'}
    encoded=json.dumps(record,indent=2)+'\n'
    if args.out:
        with open(args.out,'w',encoding='utf-8') as f:
            f.write(encoded)
        print(json.dumps({'status':'PASS','cases':record['case_count'],'out':args.out}))
    else:
        print(encoded,end='')

if __name__=='__main__':
    main()
