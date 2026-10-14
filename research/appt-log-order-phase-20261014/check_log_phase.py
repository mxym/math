#!/usr/bin/env python3
"""Finite exact certificates and numerical diagnostics for ordinary proofs.

The all-order and dimension statements are proved in the manuscripts;
neither these evaluated powers nor numerical roots are universal proofs.
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


def polynomial_shift(a, b):
    out, power = [0]*len(a), [1]
    for coefficient in a:
        for i, x in enumerate(power):
            out[i] += coefficient*x
        nxt = [0]*(len(power)+1)
        for i, x in enumerate(power):
            nxt[i] += b*x
            nxt[i+1] += x
        power = nxt
    return out


def exact_certificates():
    comparisons = [
        ('D16_geometric',128**2,3*75**2),
        ('D17_geometric',5**25,3**37),
        ('D18_geometric',448**28,255**28*3**15),
        ('D15_geometric',184**23,105**23*3**12),
        ('D15_uniform',23**23,13**23*3**12),
        ('D16_uniform',24**2,3*14**2),
        ('D18_exception',416**13,255**13*3**6),
        ('D15_exception',8**7,5**7*3**3)]
    require(all(left < right for _, left, right in comparisons), 'entropy geometric base certificates')
    require(F(163,60)*F(56,81)/2 == F(1141,1215) > F(15,16), 'entropy comparison constant')
    require(F(56,81)+F(1,540) < F(7,10), 'log2 upper rational bound')
    require(polynomial_shift([23280,-92232,25775],4)==[66752,113968,25775],
            'universal discriminant translated coefficients')
    require(polynomial_shift([-16,-3,1],8)==[24,13,1], 'rank-crossing positivity at2')
    quadratic_cases = 0
    for j in range(4,81):
        for r in (-2,-1,0,1):
            d, q = 4*j+r, 6*j+r
            a, b, c = 377*j+52*r, q*(-37*j-56*r+52), (18*j-56)*q*q
            require(a>0 and c>0 and b*b-4*a*c<0, 'finite discriminant diagnosis')
            for u in (F(1),F(3,2),F(7,3),F(j,2)):
                t, i = q+u, u+2*j+1
                left = 65*j*t*(t+q)-4*q*i*(27*q-13*t)
                require(left == a*u*u+b*u+c, 'exact stop-loss expansion')
                require(left>0, 'finite exact stop-loss positivity')
                quadratic_cases += 1
    return {'integer_entropy_certificates':[
                {'name':name,'left':str(left),'right':str(right),'strict':True}
                for name,left,right in comparisons],
            'polynomial_coefficient_identities':2,
            'finite_rational_stop_loss_checks':quadratic_cases,
            'scope':'exact scalar formulas; universal dimension proof remains written'}


def negative_controls():
    records = []
    for m,n in ((3,3),(3,4),(4,4),(3,7)):
        d = m*n
        q = [[F(0) for _ in range(d)] for _ in range(d)]
        for j in (1,2):
            x,y = j,j*n
            q[x][x] += F(1,2); q[y][y] += F(1,2)
            q[x][y] -= F(1,2); q[y][x] -= F(1,2)
        require(sum(q[i][i] for i in range(d))==2, 'rank-two trace')
        require(all(sum(q[i][k]*q[k][j] for k in range(d))==q[i][j]
                    for i,j in product(range(d),repeat=2)), 'exact orthogonal projection')
        rho = [[((1 if i==j else 0)+2*q[i][j])/(d+4)
                for j in range(d)] for i in range(d)]
        pt = [[F(0) for _ in range(d)] for _ in range(d)]
        for a,b,c,e in product(range(m),range(n),range(m),range(n)):
            pt[a*n+b][c*n+e] = rho[a*n+e][c*n+b]
        w = [F(0)]*d
        for i,s in enumerate((F(2,3),F(2,3),F(1,3))):
            w[i*n+i]=s
        require(sum(s*s for s in w)==1, 'rational Schmidt vector norm')
        expectation = sum(w[i]*pt[i][j]*w[j] for i,j in product(range(d),repeat=2))
        require(expectation==F(-1,3*(d+4)), 'actual higher-local rank-two negative PPT control')
        records.append({'m':m,'n':n,'D':d,'partial_transpose_expectation':str(expectation),
                        'positive_density_from_rank_two_projection':True,
                        'not_APPT':True})
    return records


def dec(x):
    return Decimal(x.numerator)/Decimal(x.denominator)


def moment(d,kind,j,a):
    if kind=='R':
        return (Decimal(j).ln()*(1-a)).exp()
    if kind=='P':
        z, entries = d+2*j, ((3,j),(1,d-j))
    else:
        z, entries = d-1+j, ((2,j),(1,d-1-j))
    return sum((Decimal(k)*(a*(Decimal(value)/z).ln()).exp() for value,k in entries),Decimal(0))


def scalar_g(d,a):
    x=(a*Decimal(3).ln()).exp()
    t=(Decimal(d+4)/Decimal(d+2)).ln()
    return -a*t+(2*x+d-2).ln()-(x+d-1).ln()


def finite_diagnostics():
    vertex_cases, roots = 0, []
    with localcontext() as ctx:
        ctx.prec=90
        tol=Decimal('1e-72')
        for d in range(15,49):
            for astr in ('1.001','1.125','1.5','1.875','2','3','4','20'):
                a=Decimal(astr)
                p=[moment(d,'P',j,a) for j in range(1,d-2)]
                best=max(p)
                other=[moment(d,'R',r,a) for r in range(d-2,d+1)]
                other += [moment(d,'T',j,a) for j in range(1,d-2)]
                require(max(other) < best, 'finite all-real-order envelope diagnosis')
                z=(a*Decimal(3).ln()).exp()-1
                x=Decimal(d)*(z-2*a)/(2*(a-1)*z)
                lo=max(1,min(d-3,int(x)))
                hi=max(1,min(d-3,int(x)+1))
                require(max(p[lo-1],p[hi-1])>=best*(1-tol), 'finite integer-rank diagnosis')
                vertex_cases += 1
        for d in (8,9,10,12,15,16,20,32,64,128,256):
            t=(Decimal(d+4)/Decimal(d+2)).ln()
            upper=Decimal(2).ln()/t
            low=Decimal(2)
            require(scalar_g(d,low)>0 and scalar_g(d,upper)<0, 'crossing bracket diagnosis')
            for _ in range(250):
                mid=(low+upper)/2
                if scalar_g(d,mid)>0:
                    low=mid
                else:
                    upper=mid
            tau=(low+upper)/2
            require(abs(scalar_g(d,tau))<Decimal('1e-65'), 'finite root residual')
            for a in (Decimal('.001'),Decimal('.25'),Decimal('.5'),Decimal('.75')):
                require(scalar_g(d,a)<0, 'finite subunit rank-two competitor')
            require(scalar_g(d,(1+tau)/2)>0 and scalar_g(d,tau+1)<0,
                    'finite overunit phase signs')
            derivative=-t+Decimal(3*d)*Decimal(3).ln()/((d+4)*(d+2))
            require(derivative>0, 'finite order-one entropy gap')
            f1=moment(d,'P',1,tau); f2=moment(d,'P',2,tau)
            require(abs(f1/f2-1)<Decimal('1e-65'), 'critical two ranks diagnosed')
            require(all(moment(d,'P',j,tau)<f1 for j in range(3,d-2)),
                    'critical higher-rank exclusion diagnosed')
            roots.append({'D':d,'tau_numeric':str(tau),'bracket_width':str(upper-low),
                          'equation_residual':str(scalar_g(d,tau)),
                          'numerical_scope':'scalar ratio evaluation; actual necessity only for qubit partitions'})
    return {'real_order_vertex_cases':vertex_cases,'crossing_cases':roots,
            'precision_decimal_digits':90,'independent_implementations':1,
            'scope':'finite evaluated real powers and numerical roots, not a universal proof'}


def main():
    ap=ArgumentParser(); ap.add_argument('--out',type=Path); args=ap.parse_args()
    result={'status':'PASS','kind':'supporting finite exact and numerical diagnostics',
            'new_lean':False,'unitary_sampling':False,
            'certificates':exact_certificates(),'actual_negative_controls':negative_controls(),
            'finite_diagnostics':finite_diagnostics()}
    if args.out:
        args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','integer_certificates':8,
                      'rational_stop_loss_checks':result['certificates']['finite_rational_stop_loss_checks'],
                      'actual_negative_controls':len(result['actual_negative_controls']),
                      'real_order_vertex_cases':result['finite_diagnostics']['real_order_vertex_cases'],
                      'crossing_cases':len(result['finite_diagnostics']['crossing_cases'])}))


if __name__=='__main__':
    main()
