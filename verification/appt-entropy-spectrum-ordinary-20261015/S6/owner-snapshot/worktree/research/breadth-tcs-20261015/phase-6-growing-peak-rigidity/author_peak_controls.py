"""Author exact finite regressions for actual protected pure-spike spectra.
These controls do not prove the all-state or all-sequence theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as Dec, localcontext
import datetime as dt
import hashlib
import json

def ceilq(a,b):return -((-a)//b)
def dq(q):return Dec(q.numerator)/Dec(q.denominator)
def short(q):
    with localcontext() as ctx:
        ctx.prec=32
        return str(dq(q))
def physical(m,n,alpha,beta):
    D=m*n
    assert 0<=beta<=2
    top=F(D)*(1+beta)/(D+beta)
    tail=F(D)/(D+beta)
    u=F(3*D,D+2)
    M=(top**alpha+(D-1)*tail**alpha)/D
    Tp=top**alpha/D
    r=u**alpha/D
    Htop=top**alpha-1-alpha*(top-1)
    Htail=tail**alpha-1-alpha*(tail-1)
    assert top+(D-1)*tail==D
    assert D*(M-1)==Htop+(D-1)*Htail
    assert Htop>=0 and Htail>=0 and 1<=M
    assert M>=Tp and M-Tp==F(D-1,D)*tail**alpha
    assert M!=Tp
    assert Htop+(D-1)*(tail**alpha-1)!=D*(M-1)
    with localcontext() as ctx:
        ctx.prec=48
        chi=dq(r).ln()
        h=Dec(alpha)*(dq(u)/dq(top)).ln()
        entropy=dq(M).ln()/chi
    return {'D':D,'top':top,'tail':tail,'u':u,'M':M,'Tp':Tp,'r':r,
            'chi':chi,'h':h,'entropy_relative_to_chi':entropy}

rows=[]
for k in [3,4,5,6,8,10,12]:
    m=k*k;alpha=m
    p=physical(m,m,alpha,F(2))
    assert p['top']==p['u'] and p['h']==0
    assert 0<p['M']-p['r']<1
    assert 0<(p['M']-p['r'])/p['r']<1/p['r']
    rows.append({'case':'actual_exact_ceiling_spike','k':k,'m':m,'n':m,'alpha':alpha,
      'beta_exact':'2','peak_loss_h':'0','M_over_r_decimal':short(p['M']/p['r']),
      'tail_power_sum_over_peak_decimal':short((p['M']-p['Tp'])/p['Tp']),
      'exact_trace_centering_identity':True,'wrong_omitted_trace_centering_rejected':True})

    p=physical(m,m,alpha,F(2)-F(1,k))
    assert p['top']<p['u'] and p['h']>0
    assert (p['top']/p['u'])**alpha<F(1,2)
    rows.append({'case':'credited_G_entropy_vs_sharp_moment_example','k':k,'m':m,'n':m,'alpha':alpha,
      'beta_exact':str(F(2)-F(1,k)),
      'h_decimal':str(p['h']),'h_over_chi_decimal':str(p['h']/p['chi']),
      'M_over_r_decimal':short(p['M']/p['r']),
      'logM_over_chi_decimal':str(p['entropy_relative_to_chi']),
      'interpretation':'Finite illustration of the credited asymptotic distinction; exact all-unitary APPT because beta in[0,2]'})

    n=ceilq(3**alpha,m*2**k)
    assert n>=m
    p=physical(m,n,alpha,F(2)-F(3,k))
    assert 0<p['chi'] and p['h']>p['chi']
    upper=F(2**k)*(1-F(1,k))**alpha
    assert p['Tp']<=upper<1 and p['M']<2
    rows.append({'case':'actual_near_window_rejects_bare_peak_convergence','k':k,'m':m,'n':str(n),'alpha':alpha,
      'beta_exact':str(F(2)-F(3,k)),
      'integer_dimension_rule':'n=ceil(3^alpha/(m*2^k)); chi~k log2, h~k',
      'chi_decimal':str(p['chi']),'h_decimal':str(p['h']),
      'h_over_chi_decimal':str(p['h']/p['chi']),
      'h_over_alpha_decimal':str(p['h']/Dec(alpha)),
      'peak_actual_normalized_decimal':short(p['top']),
      'actual_peak_moment_decimal':short(p['Tp']),
      'logM_over_chi_decimal':str(p['entropy_relative_to_chi']),
      'exact_inequality_verified':'Tp<=2^k*(1-1/k)^(k^2)<1 and M<2',
      'relation_to_manuscript':'Rational-ceiling parallel actual path, not the paper exp(-k) path; both expose chi/alpha->0'})

paper=Path(__file__).with_name('PAPER.md')
source=Path(__file__)
out={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
 'scope':'Author finite physical regressions, not independent ordinary review, universal search or Lean',
 'paper_sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'arithmetic':'All spectra, normalization, identities and inequalities use standard-library Fraction/integers; log displays only use Decimal48',
 'rows':rows,'finite_cases':len(rows),'all_requested_assertions_passed':True,
 'claimed_optimum_in_controls':'No exact finite M* value; logM/chi is explicitly relative to the proved asymptotic value only',
 'not_proof_of_quantified_asymptotic_claim':True}
dest=source.with_name('AUTHOR_EXACT_CONTROLS.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':out['paper_sha256'],'source_sha256':out['source_sha256'],
 'finite_cases':len(rows),'all_requested_assertions_passed':True,'result_bytes':dest.stat().st_size},indent=2))
