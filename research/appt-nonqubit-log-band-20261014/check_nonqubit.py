#!/usr/bin/env python3
"""Exact physical controls and finite diagnostics, not a universal proof.

The real-order and dimension statements are proved in PAPER.md. This one
standard-library implementation is run on Windows and WSL, including -O.
"""
from argparse import ArgumentParser
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def exact_certificates():
    tests = {
        'continuous_band_base': 9**32 > 577**11,
        'tail_constant': F(11,8)*F(7,5) == F(77,40) < 2,
        'log3_upper_atanh_remainder': 2*(F(1,2)+F(1,24))+F(1,60) == F(11,10) < F(9,8),
        'log2_upper_atanh_remainder': F(56,81)+F(1,540) < F(7,10),
        'derivative_base': 9**4 > 18**3,
        'derivative_comparison': F(128,3) < F(576,11),
        'near_cap_ratio': F(11,12)/F(5,6) == F(11,10),
        'qubit_moment_first_factor': 3**8 > 4097,
        'qubit_Bernoulli': 1-F(300,2050) == F(35,41),
        'qubit_order_above_false_band': 32*12*F(7,10)+1 < 300,
    }
    require(all(tests.values()), 'one of the displayed exact scalar certificates failed')
    x = 3**300
    ratio = (F(2049,2050)**300)*F(2*x+4094,x+4095)
    require(ratio > F(105,82) > 1, 'actual qubit rank-two moment countercontrol')
    return {'certificates': tests,
            'qubit_control': {'pair':[2,2048], 'D':4096, 'alpha':300,
                'actual_APPT_family':'(I+2Q)/(D+4), rank(Q)=2; credited qubit projection theorem',
                'moment_ratio_strict_lower_bound':'105/82',
                'above_32_logD_plus1':True, 'not_a_large_matrix_sampling_check':True}}


def physical_controls():
    out = []
    for m,n in ((3,3),(3,4),(4,4),(3,7)):
        d = m*n
        q = [[F(0) for _ in range(d)] for _ in range(d)]
        for j in (1,2):
            x,y = j,j*n
            q[x][x] += F(1,2); q[y][y] += F(1,2)
            q[x][y] -= F(1,2); q[y][x] -= F(1,2)
        require(sum(q[i][i] for i in range(d))==2, 'projection trace')
        require(all(sum(q[i][k]*q[k][j] for k in range(d))==q[i][j]
                    for i,j in product(range(d),repeat=2)), 'actual orthogonal projection')
        w = [F(0)]*d
        for i,s in enumerate((F(2,3),F(2,3),F(1,3))):
            w[i*n+i] = s
        require(sum(s*s for s in w)==1, 'unit Schmidt witness')
        expectation = sum(w[a*n+b]*q[a*n+e][c*n+b]*w[c*n+e]
                          for a,b,c,e in product(range(m),range(n),range(m),range(n)))
        require(expectation==F(-2,3), 'rank-two physical witness')
        for epsilon in (F(0),F(1,100*(d+3))):
            a = F(5,2*(d+3))+epsilon
            b = (1-2*a)/(d-2)
            value = b+(a-b)*expectation
            require(b>0 and 2*a+(d-2)*b==1, 'genuine density with actual spectrum')
            require(value == -F(2*(d+3),3*(d-2))*epsilon, 'second-eigenvalue cap expansion')
            require((value==0) if epsilon==0 else (value<0), 'cap/violation physical control')
            out.append({'pair':[m,n], 'D':d, 'epsilon':str(epsilon),
                        'actual_density_spectrum':'(a,a,b,...,b)',
                        'partial_transpose_expectation':str(value),
                        'cap_necessity_only':True, 'APPT_sufficiency_not_inferred':True})
    return out


def dfrac(x):
    return Decimal(x.numerator)/Decimal(x.denominator)


def scalar_diagnostics():
    rows = []
    for d in (9,12,16,21,30,64,128,1024,8192,10**8):
        D = Decimal(d); u = 3*D/(D+2)
        t0 = 32*D.ln()
        for T in (t0,t0+Decimal('0.5'),t0*Decimal('1.01'),2*t0):
            ratio = (Decimal('1.1').ln()*T).exp()/(1+T*(D-1))
            far = (D/u)*(-T/12).exp()
            require(ratio>1 and far<1, 'finite real-power near/far diagnostic')
            rows.append({'D':d,'T':str(T),'near_cap_scalar_ratio':str(ratio),
                         'far_region_ratio_bound':str(far)})
    # A finite grid in the necessary spectral relaxation, explicitly not an
    # APPT classification or a proof for all dimensions/orders.
    spectra = 0
    for d in (9,12,16,21,30,64,128):
        u,V = F(3*d,d+2),F(5*d,2*(d+2))
        for denominator in (12,24,120,120000,6,2):
            delta = u/denominator; p = u-delta; mu = (d-p)/(d-1)
            for k in (1,2,(d-1)//2):
                for fraction in (F(0),F(1,4),F(1,2),F(1)):
                    # k high tails and d-1-k low tails; stay within all used
                    # necessary constraints before evaluating any moment.
                    h = fraction*min(V-mu, p-mu, mu*F(d-1-k,k),delta*F(d-1-k,3*k))
                    if h<0:
                        continue
                    tail = [mu+h]*k+[mu-F(k,d-1-k)*h]*(d-1-k)
                    y = sorted([p]+tail,reverse=True)
                    require(sum(y)==d and y[-1]>=0 and y[0]==p, 'necessary-spectrum trace and ordering')
                    require(sum(y[-3:])>=p and y[1]<=V, 'necessary linear and tail constraints')
                    variance = sum((x-mu)**2 for x in tail)
                    require(min(tail)>=mu-2*delta and variance<=2*(d-1)*V*delta,
                            'finite exact tail and variance checks')
                    T = 32*Decimal(d).ln(); alpha = T+1
                    value = sum((alpha*dfrac(x).ln()).exp() if x>0 else Decimal(0) for x in y)
                    pole = (alpha*dfrac(u).ln()).exp()+(d-1)*(alpha*dfrac(F(d,d+2)).ln()).exp()
                    require(value<pole, 'finite necessary-spectrum real-order diagnostic')
                    spectra += 1
    return {'scalar_real_order_cases':len(rows),'scalar_rows':rows,
            'necessary_relaxation_spectra_checked':spectra,
            'scope':'finite diagnostics, not all-state or all-order proof; spectra are not asserted APPT'}


def lower_scale_diagnostics():
    rows = []
    for exponent in (6,20,40,80,160):
        d = 3*10**exponent; D = Decimal(d)
        for c in (Decimal('0.5'),Decimal(1),Decimal(2),Decimal('2.4')):
            alpha = c*D.ln()
            r = int(D/alpha); theta = Decimal(r)/D
            projection = (1-theta+theta*(alpha*Decimal(2).ln()).exp())/((alpha*(1+theta).ln()).exp())
            pole = ((alpha*Decimal(3).ln()).exp()+D-1)/D * (alpha*(D/(D+2)).ln()).exp()
            ratio = projection/pole
            # Only the asymptotic theorem covers all sufficiently large D;
            # the slow approach at c=2.4 is visible rather than suppressed.
            if exponent==160:
                require(ratio>1, 'large finite actual 3xn APPT competitor')
            rows.append({'D':str(d),'pair':['3',str(d//3)],'c':str(c),'alpha':str(alpha),
                         'rank':str(r),'moment_ratio':str(ratio),'beats_pole':ratio>1,
                         'APPT_by_written_projection_criterion':True,'ASEP_not_claimed':True})
    return rows


def main():
    parser = ArgumentParser(); parser.add_argument('--out',type=Path)
    args = parser.parse_args()
    with localcontext() as ctx:
        ctx.prec = 210
        record = {'status':'PASS','kind':'finite exact certificates and finite numerical diagnostics',
            'universal_proof':'PAPER.md, not these diagnostics','implementation_count':1,
            'precision_digits':ctx.prec,'exact':exact_certificates(),'physical_controls':physical_controls(),
            'scalar_diagnostics':scalar_diagnostics(),'lower_scale_diagnostics':lower_scale_diagnostics(),
            'new_lean_execution':False,'new_audit_roots':0}
    if args.out:
        args.out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':record['status'],'exact_scalar_certificates':len(record['exact']['certificates']),
        'physical_second_eigenvalue_controls':len(record['physical_controls']),
        'scalar_real_order_cases':record['scalar_diagnostics']['scalar_real_order_cases'],
        'necessary_spectral_cases':record['scalar_diagnostics']['necessary_relaxation_spectra_checked'],
        'actual_3xn_lower_scale_cases':len(record['lower_scale_diagnostics']),
        'qubit_restriction_control':'actual D4096 alpha300, strict moment ratio >105/82',
        'implementation_count':1,'universal_proof_not_inferred':True}))


if __name__=='__main__':
    main()
