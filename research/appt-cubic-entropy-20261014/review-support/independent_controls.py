from fractions import Fraction as F
from itertools import permutations, combinations
from pathlib import Path
import json, hashlib, sympy as s

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent

# Fixed-label enumeration is independent of the author's vertex-creation generator.
def inverse_quadratic(H):
    n=len(H); L=[[F(i==j) for j in range(n)] for i in range(n)]; d=[]
    for i in range(n):
        di=H[i][i]-sum(L[i][k]*L[i][k]*d[k] for k in range(i))
        if di<=0:return None
        d.append(di)
        for j in range(i+1,n):
            L[j][i]=(H[j][i]-sum(L[j][k]*L[i][k]*d[k] for k in range(i)))/di
    w=[]
    for i in range(n):w.append(F(1)-sum(L[i][k]*w[k] for k in range(i)))
    return sum(w[i]*w[i]/d[i] for i in range(n))

def exhaustive(p,b):
    h=2*(len(p)+len(b))
    edges=list(combinations(range(h),2))
    positive=[('d',i) for i in range(h)]+[('e',e) for e in edges]
    count=0; best=F(0)
    for pe in permutations(edges,len(p)):
        for bs in permutations(positive,len(b)):
            P=[[F(0) for j in range(h)] for i in range(h)]
            for v,(i,j) in zip(p,pe):P[i][j]+=v;P[j][i]+=v
            for v,(tag,slot) in zip(b,bs):
                if tag=='d':P[slot][slot]+=2*v
                else:
                    i,j=slot;P[i][j]+=v;P[j][i]+=v
            H=[[2*F(i==j)-P[i][j] for j in range(h)] for i in range(h)]
            iq=inverse_quadratic(H);count+=1
            if iq is None:return None,count
            C=4*(iq-F(h,2))
            if C>best:best=C
    return best,count

x,y,z=s.symbols('x y z',nonnegative=True)
k,m,K=s.symbols('k m K',positive=True)
a=2+k;c=m*m*(2/(m-1)-k)
assert s.factor((1/k-m/a)-c*(m-1)/(k*m*m*a))==0
H=s.Matrix([[2*(1-y),-z],[-z,2]])
C=4*((s.ones(2,1).T*H.inv()*s.ones(2,1))[0]-1)
neg_gap=2*z*(4*(1-y)*(y-z)+z*(2-y-z))/((1-y)*(1-z)*(4-4*y-z*z))
assert s.factor(C-2*y/(1-y)-2*z/(1-z)-neg_gap)==0
square=(x*x+2*x+2*y)**2-(x*x+y*y)*(x+2-y)**2
assert s.factor(square-y*(2*x*(x+2)*(x+2-y)+y*y*(2*x+4-y)))==0
u,v,b=s.symbols('u v b',nonnegative=True)
P=s.Matrix([[2*b,u,v],[u,0,0],[v,0,0]])
ones=s.ones(3,1);C3=4*((ones.T*(2*s.eye(3)-P).inv()*ones)[0]-s.Rational(3,2))
U=u+v;S=u*u+v*v
assert s.factor(C3-2*(U*U+4*U+S+4*b)/(4*(1-b)-S))==0

# Verify the normalization kernel and interval optimum independently to cubic order.
alpha,t,theta=s.symbols('alpha t theta')
Ap=sum(s.prod(alpha-j for j in range(i))*t**i/s.factorial(i) for i in range(1,6))
theta_series=s.simplify(s.series((Ap-alpha*t)/((alpha-1)*t*Ap),t,0,3).removeO())
assert s.simplify(theta_series.subs(t,0)-s.Rational(1,2))==0
assert s.simplify(s.diff(theta_series,t).subs(t,0)+(alpha+1)/12)==0
th=s.Rational(1,2)-(alpha+1)*t/12
logpow=s.series(s.log(1+th*Ap),t,0,4).removeO()
logmean=s.series(alpha*s.log(1+th*t),t,0,4).removeO()
B=s.simplify((logpow-logmean)/(alpha-1))
assert s.simplify(s.expand(B).coeff(t,2)-alpha/8)==0
assert s.simplify(s.expand(B).coeff(t,3)+alpha/8)==0

source_report=json.loads((SOURCE/'FINITE_CONTROLS.json').read_text())
records=[]
for rec in source_report['exact_profile_controls']:
    p=list(map(F,rec['p'])); b=list(map(F,rec['beta']))
    if len(p)+len(b)>3:continue
    C,count=exhaustive(p,b)
    assert C==F(rec['cost'])
    disjoint=sum(4*v/(2-v) for v in p)+sum(2*v/(1-v) for v in b)
    assert C>=disjoint
    if len(p)+len(b)>1:assert C>disjoint
    records.append({'p':rec['p'],'beta':rec['beta'],'fixed_label_assignments':count,'cost':str(C),'matches_author_profile_value':True})

# Actual matrix with one positive head: use direct m by m LDL rather than the reduced K.
actual=[]
for mi in [6,12,24]:
    for pi,ci,expected in [(F(1),F(41,10),True),(F(1),F(2),False),(F(1),F(0),False)]:
        ki=F(2,mi-1)-ci/(mi*mi)
        H=[[F(2+ki)*(i==j)-ki for j in range(mi)] for i in range(mi)]
        H[0][1]-=pi;H[1][0]-=pi
        passed=inverse_quadratic(H) is not None
        assert passed==expected
        actual.append({'m':mi,'p':str(pi),'c':str(ci),'full_matrix_positive_definite':passed})

report={'scope':'Independent ordinary review controls; finite calculations do not establish the infinite theorem.',
        'symbolic_checks':['finite rank-one prefactor','two-negative cost and strict gap','shifted-star square identity','three-vertex full inverse star formula','interval optimum Taylor slope','interval deficit quadratic and cubic coefficients'],
        'fixed_label_graph_enumeration':records,'full_matrix_LDL_checks':actual,
        'author_report_read_scope':'Parsed complete JSON, all keys and every profile; used only listed exact cost values as comparisons, not proof inputs.',
        'source_sha256':{name:hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() for name in ['INITIAL_PAPER.md','PAPER.md','THEOREM_MAP.md','check_cubic.py','FINITE_CONTROLS.json']}}
(HERE/'independent_controls.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'symbolic_checks':len(report['symbolic_checks']),'fixed_label_graph_assignments':sum(x['fixed_label_assignments'] for x in records),'profiles':len(records),'full_matrix_LDL_checks':len(actual),'all_passed':True}))