"""Exact finite SOS/physical negative controls and growing-order diagnostics.

These auxiliary checks do not replace the all-dimension analytic proof.
Only the Python standard library is needed; ordinary and -O runs agree.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from itertools import combinations
import hashlib,json,math,pathlib,sys

def require(condition,message):
    if not condition: raise ArithmeticError(message)

def coefficients(m,H):
    c=F(2,m+H)
    q=2-(m-3)*c
    a=2-2*(m-2)*c*c/q
    d=a-c
    require(q>0 and c>0 and d>=0,'physical coefficients')
    require((2-a)*q==2*(m-2)*c*c,'boundary determinant')
    require(d*q==(2-(m-1)*c)*(2+c),'spike nonnegativity identity')
    return c,a,d

def quadratic(s,c,d):
    return sum(x*x for x in s)-c*sum(s[i]*s[j] for i,j in combinations(range(len(s)),2))-d*s[0]*s[1]

identities=0
for m in [3,4,5,8,12,24]:
    for H in [0,1,2,4,9,21]:
        c,a,d=coefficients(m,H)
        r=m-2; R=(1-c*(r-1)/2)/r
        require(R>0,'tail Schur coefficient')
        for phase in range(7):
            s=[F(((i+2)*(phase+1))%11-4,(i%3)+1) for i in range(m)]
            A=s[0]+s[1]; B=s[0]-s[1]
            T=sum(s[2:]); Q=sum(x*x for x in s[2:])
            rhs=(2+c+d)*B*B/4+(1+c/2)*(Q-T*T/r)+R*(T-c*A/(2*R))**2
            require(quadratic(s,c,d)==rhs,'exact continuum SOS identity')
            require(rhs>=0,'signed scalar SOS nonnegativity')
            identities+=1

# A real 5x5-system density with the mistaken quarter-strength protection
# actually has a negative partial-transpose quadratic form. P is the entire
# 10-dimensional antisymmetric subspace and v the (0,1) antisymmetric vector.
m=5; D=m*m; c=F(1,4); r=m-2
R=(1-c*(r-1)/2)/r
wrong_d=2-c-r*c*c/(4*(1-c*(r-1)/2))
s=[F(1),F(1),F(1,3),F(1,3),F(1,3)]
require(quadratic(s,c,wrong_d)==F(-3,16),'wrong-cross-term scalar control')
M=[[F(int(i==j)) for j in range(D)] for i in range(D)]
for i,j in combinations(range(m),2):
    u=i*m+j; v=j*m+i
    weight=c+(wrong_d if (i,j)==(0,1) else 0)
    M[u][u]+=weight/2; M[v][v]+=weight/2
    M[u][v]-=weight/2; M[v][u]-=weight/2
trace=sum(M[i][i] for i in range(D))
pt=[[F(0) for j in range(D)] for i in range(D)]
for i in range(D):
    a,b=divmod(i,m)
    for j in range(D):
        k,l=divmod(j,m)
        pt[a*m+l][k*m+b]=M[i][j]/trace
psi=[s[i//m] if i//m==i%m else F(0) for i in range(D)]
physical=sum(psi[i]*pt[i][j]*psi[j] for i in range(D) for j in range(D))/sum(x*x for x in s)
require(physical<0,'actual negative-PPT control must fail')
require(physical==quadratic(s,c,wrong_d)/(trace*sum(x*x for x in s)),'actual transpose normalization')

def dec(x):
    return Decimal(x.numerator)/Decimal(x.denominator) if isinstance(x,F) else Decimal(x)

diagnostics=[]
with localcontext() as ctx:
    ctx.prec=75
    for m,alpha in [(256,4),(4096,8),(65536,16),(1048576,32),(16777216,64)]:
        H=math.isqrt(alpha*m)
        if H*H<alpha*m: H+=1
        c,a,d=coefficients(m,H)
        for label,n in [('square',m),('broad',m*(3**alpha)),('moment-crossover',m*(3**alpha)//(alpha*(alpha-1)//2))]:
            D=m*n; k=((m-1)*n+1)//2
            Z=F(D)+k*c+d
            y1=F(D)*(1+a)/Z
            hi=F(D)*(1+c)/Z; lo=F(D)/Z
            mu=F(3*D,D+2)
            M=(dec(y1)**alpha+(k-1)*dec(hi)**alpha+(D-k)*dec(lo)**alpha)/D
            target=dec(mu)**alpha/D+Decimal(alpha*(alpha-1))/(2*m*m)
            ratio=(M-1)/target
            require(M>1 and ratio>0,'positive normalized excess')
            diagnostics.append({'m':m,'alpha':alpha,'aspect_case':label,'n':str(n),'H':H,
                'explicit_state_to_asymptotic_target':str(ratio),'alpha_peak_log_gap':str(alpha*(dec(mu)/dec(y1)).ln())})

result={'kind':'Finite exact auxiliary checks; analytic universal proofs are separate',
 'exact_sos_specializations':identities,'actual_negative_ppt_control':str(physical),
 'physical_control_normalization':'Actual partial transpose of a rational 25x25 density; normalized rational Schmidt test',
 'growth_diagnostics':diagnostics,'assertions_disabled':not __debug__,
 'scope_exclusions':['not an all-APPT optimizer search','not a Lean proof','not external peer review'],
 'status':'PASS'}
if '--output' in sys.argv:
    out=pathlib.Path(sys.argv[sys.argv.index('--output')+1])
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','sos_checks':identities,'actual_negative_ppt':str(physical),
 'diagnostic_cases':len(diagnostics),'last_diagnostic':diagnostics[-1]},indent=2))
