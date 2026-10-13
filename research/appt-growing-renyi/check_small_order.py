"""Exact negative-family identities/physical controls and zero-order diagnostics.

The universal theorem and classification are proved in the mathematical note;
these are auxiliary finite and numerical checks, not replacement proofs.
"""
from fractions import Fraction as F
from decimal import Decimal,localcontext,ROUND_CEILING,ROUND_FLOOR
from itertools import combinations
import json,math,pathlib,sys

def require(ok,msg):
    if not ok: raise ArithmeticError(msg)

exact=0
for m in [2,3,4,5,8,12,25]:
    for H in [1,2,3,4,9,14,25]:
        if H>m: continue
        b=(H+1)*m; d=b-H*H
        require(d>=0,'admissible negative spike')
        for phase in range(7):
            s=[F(((i+2)*(phase+1))%11-4,(i%3)+1) for i in range(m)]
            T=sum(s[1:]); Q=sum(x*x for x in s[1:]); r=m-1
            lhs=b*sum(x*x for x in s)-2*H*sum(s[i]*s[j] for i,j in combinations(range(m),2))-d*s[0]*s[0]
            rhs=(H*s[0]-T)**2+(H+1)*(r*Q-T*T)+(2*H+1)*Q
            require(lhs==rhs and rhs>=0,'negative-family continuum SOS')
            exact+=1

# Deleting the H^2 protector fails on an actual 2x2-system rational density.
# P is the antisymmetric projection and v=|00> is orthogonal to its range.
B=[[F(0),F(0),F(0),F(0)],
   [F(0),F(5),F(-1),F(0)],
   [F(0),F(-1),F(5),F(0)],
   [F(0),F(0),F(0),F(4)]]
trace=sum(B[i][i] for i in range(4))
pt=[[F(0) for j in range(4)] for i in range(4)]
for i in range(4):
    a,b=divmod(i,2)
    for j in range(4):
        c,d=divmod(j,2)
        pt[2*a+d][2*c+b]=B[i][j]/trace
psi=[F(3),F(0),F(0),F(1)]
physical=sum(psi[i]*pt[i][j]*psi[j] for i in range(4) for j in range(4))/sum(x*x for x in psi)
require(physical==F(-1,70),'actual unprotected negative-PPT control')

def dec(x):
    return Decimal(x.numerator)/Decimal(x.denominator) if isinstance(x,F) else Decimal(x)

diagnostics=[]
for exponent in [20,40,80,160]:
    with localcontext() as ctx:
        ctx.prec=2*exponent+90
        m=10**exponent
        for tau in [Decimal('0.1'),Decimal(1),Decimal(4)]:
            alpha=tau/Decimal(m).ln()
            critical=2*(-tau).exp()
            for label,factor in [('below',Decimal('0.5')),('critical',Decimal(1)),('above',Decimal(2))]:
                c=critical*factor
                n=int((c*Decimal(m)/alpha).to_integral_value(rounding=ROUND_CEILING))
                n=max(m,n); D=m*n
                root=math.isqrt(m)
                H=root if 1/alpha.sqrt()>=Decimal(root).ln() else int((1/alpha.sqrt()).exp().to_integral_value(rounding=ROUND_FLOOR))
                H=max(1,H)
                b=(H+1)*m; d=b-H*H; k=D//2
                Z=(D-1)*b+2*H*k+H*H
                ell=F(D*H*H,Z); hi=F(D*(b+2*H),Z); lo=F(D*b,Z)
                M=(k*(alpha*dec(hi).ln()).exp()+(D-k-1)*(alpha*dec(lo).ln()).exp()+(alpha*dec(ell).ln()).exp())/D
                DE=Decimal(D)*M.ln()/(alpha-1)
                target=max(Decimal(1),1-(-alpha*Decimal(m).ln()).exp()+alpha*Decimal(n)/(2*m))
                singular=Decimal(D)*(Decimal(D)/Decimal(D-1)).ln()
                realized=max(DE,singular)
                require(M>0 and M<1 and DE>0,'physical small-order deficit')
                diagnostics.append({'m_decimal_exponent':exponent,'tau':str(tau),'c_branch':label,
                    'alpha':str(alpha),'H_digits':len(str(H)),
                    'full_rank_deficit_coefficient':str(DE),'singular_deficit_coefficient':str(singular),
                    'target':str(target),'best_explicit_to_target':str(realized/target),
                    'least_eigenvalue_power':str((alpha*dec(ell).ln()).exp())})

result={'kind':'Exact finite auxiliary identities, actual quantum negative control, numerical growing-window diagnostics',
 'negative_sos_specializations':exact,'actual_unprotected_negative_ppt':str(physical),
 'diagnostic_cases':len(diagnostics),'growth_diagnostics':diagnostics,
 'assertions_disabled':not __debug__,
 'scope_exclusions':['not a universal-proof replacement','not a Lean theorem','not external peer review'],
 'status':'PASS'}
if '--output' in sys.argv:
    p=pathlib.Path(sys.argv[sys.argv.index('--output')+1]); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','exact_sos':exact,'actual_negative_ppt':str(physical),
 'diagnostics':len(diagnostics),'last_diagnostic':diagnostics[-1]},indent=2))
