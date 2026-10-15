"""Exact finite physical projection controls for the fourth-root sharpness.
No exact finite E_alpha value is claimed. Decimal entropy displays are diagnostic.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as Dec, localcontext
import datetime as dt
import hashlib
import json

def dq(q):return Dec(q.numerator)/Dec(q.denominator)
rows=[]
for l in [4,6,8,10,12,16,20,24]:
    m=l**4;n=m*m;D=m*n;gamma=F(n,m)
    k=D//2+D//l
    theta=F(k,D);c=F(2,m-1)
    assert D%2==0 and D%l==0 and theta==F(1,2)+F(1,l) and 0<k<D
    assert 1-c*F(m-1,2)==0
    high=(1+c)/(1+c*theta);low=1/(1+c*theta)
    assert k*high+(D-k)*low==D and high>low>0
    s=F(m)*c/(1+c*theta)
    assert s==F(2*m)/(m+F(2,l))
    Xlo=m*(low-1);Xhi=m*(high-1)
    assert Xlo==-s*theta and Xhi==s*(1-theta)
    q=((1-theta)*Xlo**2+theta*Xhi**2)
    assert q==s*s*theta*(1-theta)
    assert q==(1-F(4,l*l))/(1+F(2,l*m))**2
    W2sq=(1-theta)*(Xlo+1)**2+(theta-F(1,2))*(Xhi+1)**2+F(1,2)*(Xhi-1)**2
    assert W2sq==1+q-2*s*(1-theta)
    assert 0<1-q-F(4,l*l)<=F(4,l**5)
    assert abs(W2sq-(F(4,l)-F(4,l*l)))<=F(10,l**5)
    assert F(l,2)<W2sq/(1-q)<l
    assert 1<W2sq**2/(1-q)<4
    M2=(1-theta)*low**2+theta*high**2
    M3=(1-theta)*low**3+theta*high**3
    assert M2==1+q/F(m*m)
    Q=gamma*q
    H3=lambda y:y**3-1-3*(y-1)
    assert D*(M3-1)==(D-k)*H3(low)+k*H3(high)
    assert D*(M3-1)!=(D-k)*low**3+k*high**3
    with localcontext() as ctx:
        ctx.prec=50
        e1=(1-dq(theta))*dq(low)*dq(low).ln()+dq(theta)*dq(high)*dq(high).ln()
        e2=dq(M2).ln()
        e3=dq(M3).ln()/2
        displays={str(a):str(Dec(2*m*m)*e/Dec(a)) for a,e in [(1,e1),(2,e2),(3,e3)]}
    rows.append({'case':'actual_exact_rank_projection_fourth_root_sharpness','l':l,'m':m,'n':n,'D':D,'rank_k':k,
      'theta_exact':str(theta),'c_exact':str(c),'s_exact':str(s),
      'q_exact':str(q),'W2_squared_exact':str(W2sq),
      'W2_squared_over_variance_gap_exact':str(W2sq/(1-q)),
      'W2_fourth_over_variance_gap_exact':str(W2sq**2/(1-q)),
      'entropy_scaled_by_alpha_over_2m2_decimal':displays,
      'actual_APPT_sufficiency':'For every globalU and Schmidt witness Tr(UPU*W)>=-(m-1)/2; exact 1-c(m-1)/2=0, analytic proof in PAPER',
      'finite_assertions':['Actual integer rank','Trace normalization','Physical witness coefficient','Exact rescaled law/variance','Exact optimal monotone W2 cost','Joint scale asymptotic remainder inequalities','Exact centered real-power identities'],
      'not_finite_optimum':'E_alpha is not computed or replaced by the lower family in these controls'})

outside=[]
for k in [4,8,16,32]:
    m=k;n=k*k;D=m*n;alpha=F(1,k*k);gamma=F(n,m)
    q=F(m*m,D-1)
    entropy_scaled_lower=F(2*m*m)/(alpha*D)
    assert alpha*gamma==F(1,k) and entropy_scaled_lower==2*k and q<1
    outside.append({'case':'outside_domain_actual_singular_pole','k':k,
      'actual_state':'(I-vv*)/(D-1); all-unitary APPT by pure PT largest eigenvalue<=1',
      'q_exact':str(q),'alpha_gamma_exact':str(alpha*gamma),
      'scaled_entropy_rigorous_lower_bound_exact':str(entropy_scaled_lower),
      'bound':'log(D/(D-1))>=1/D, all positive orders',
      'meaning':'Rejects dropping alpha gamma->infinity from the stated bulk profile'})

paper=Path(__file__).with_name('PAPER.md');source=Path(__file__)
out={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
 'scope':'Author finite exact physical regressions only; not universal proof, independent review or Lean',
 'paper_sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'arithmetic':'Fraction and integers for every identity/inequality/rank/W2; Decimal50 only for clearly labeled entropy diagnostics',
 'actual_projection_cases':rows,'actual_outside_domain_cases':outside,
 'finite_cases':len(rows)+len(outside),'all_requested_assertions_passed':True,
 'not_proof_of_universal_theorems':True,'no_exact_finite_optimum_used':True}
dest=source.with_name('AUTHOR_EXACT_CONTROLS.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':out['paper_sha256'],'source_sha256':out['source_sha256'],
 'finite_cases':out['finite_cases'],'all_requested_assertions_passed':True,'result_bytes':dest.stat().st_size},indent=2))
