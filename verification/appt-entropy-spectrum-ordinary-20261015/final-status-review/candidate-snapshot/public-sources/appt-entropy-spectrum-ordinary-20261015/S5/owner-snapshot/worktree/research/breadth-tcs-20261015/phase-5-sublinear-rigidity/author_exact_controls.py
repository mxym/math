"""Exact finite regressions for physical counterexamples and body centering.
These are author controls, not a proof of the all-sequence rigidity theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import datetime as dt
import hashlib
import json

def ceilq(a,b):return -((-a)//b)
def moment_pole(m,n,alpha):
    D=m*n
    u=F(3*D,D+2);tail=F(D,D+2)
    M=(u**alpha+(D-1)*tail**alpha)/D
    U=u**alpha;V=F(alpha*(alpha-1),2)*F(n,m)
    Q=F(4*D*(D-1),(D+2)**2)
    return {'M':M,'U':U,'V':V,'Q':Q,'D':D}

rows=[]
for alpha in [4,6,8,12,16,24]:
    m=alpha**2
    n=ceilq(2*m*3**alpha,alpha*(alpha-1))
    p=moment_pole(m,n,alpha)
    ratio=(p['M']-1)*p['D']/(p['U']+p['V'])
    wp=p['U']/(p['U']+p['V'])
    assert 0<ratio<F(3,4)
    rows.append({'case':'balanced_actual_pole_rejects_branch_min','alpha':alpha,'m':m,'n':n,
      'wp_exact':str(wp),'h_exact':'0','db_exact':'5/2',
      'normalized_moment_excess_using_credited_G1_equivalent':str(ratio),
      'wrong_branch_min_exact':'0','actual_state':'(I+2vv*)/(D+2) with original all-unitary APPT proof credited'})

    n=m*3**(2*alpha)
    D=m*n;gamma=F(n,m)
    assert D%4==0
    R=m*(m-1)//2;K=m*(m+1)//2;N=D-m*m+2
    high=D//4-(R-1);mid=D//2;low=D//4-(K-1)
    assert min(high,mid,low)>0 and high+mid+low==N
    yp=F(m+1,m);ym=F(1);yl=F(m-1,m)
    mu=(high*yp+mid*ym+low*yl)/N
    A=yl;kappa=yp/yl-1;L=(m-1)*kappa
    theta=(mu/A-1)/kappa
    J=F(mid,N)
    QB=high*(yp-1)**2+low*(yl-1)**2
    rhs=F(N,D)*F(m,m-1)**2*A*A*(L*L*theta*(1-theta)-J)+F(m*m*N,D)*(mu-1)**2
    assert rhs==QB/gamma and mu-1==F(1,N)
    assert rhs-F(m*m*N,D)*(mu-1)**2!=QB/gamma
    Q=F(D,2*m*m)
    assert Q/gamma==F(1,2) and L==2
    M=(yl**alpha+2+yp**alpha)/4
    u=F(3*D,D+2);U=u**alpha;V=F(alpha*(alpha-1),2)*gamma
    ratio=(M-1)*D/(U+V)
    assert 0<ratio<F(3,5)
    rows.append({'case':'physical_three_level_rejects_omitting_J','alpha':alpha,'m':m,'n':n,
      'L_exact':str(L),'theta_minus_half_exact':str(theta-F(1,2)),'J_exact':str(J),
      'total_Q_over_gamma_exact':str(Q/gamma),
      'actual_mean_minus_one_exact':str(mu-1),'centered_variance_identity_exact':True,
      'omitting_actual_mean_term_rejected':True,
      'normalized_moment_excess_using_credited_G1_equivalent':str(ratio),
      'actual_state':'(I+[2/(m-1)]X)/Tr(I+[2/(m-1)]X), X spectrum0,1/2,1 with multiplicitiesD/4,D/2,D/4',
      'all_unitary_APPT':'Analytic operator interval witness argument in PAPER.md, not inferred from sampling'})

    p=moment_pole(m,m,alpha)
    ratio=(p['M']-1)*p['D']/(p['U']+p['V'])
    rows.append({'case':'square_actual_pole_keeps_bulk_weight','alpha':alpha,'m':m,'n':m,
      'Q_over_gamma_exact':str(p['Q']),
      'wb_exact':str(p['V']/(p['U']+p['V'])),
      'normalized_moment_excess_using_credited_G1_equivalent':str(ratio),
      'interpretation':'Bulk variance need not approach one when its weight vanishes'})

paper=Path(__file__).with_name('PAPER.md')
source=Path(__file__)
out={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
     'scope':'Author exact finite physical regressions only; not independent review, global search, or Lean',
     'paper_sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
     'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
     'arithmetic':'Python standard-library Fraction and integers only',
     'rows':rows,'finite_cases':len(rows),
     'all_requested_assertions_passed':True,
     'not_proof_of_quantified_asymptotic_claim':True}
dest=source.with_name('AUTHOR_EXACT_CONTROLS.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':out['paper_sha256'],'source_sha256':out['source_sha256'],
                  'finite_cases':len(rows),'all_requested_assertions_passed':True,
                  'result_bytes':dest.stat().st_size},indent=2))
