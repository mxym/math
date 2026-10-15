"""Exact author regressions for actual compressed centered spectra.
No finite optimum or universal asymptotic rate is inferred from this script.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as Dec,localcontext
from collections import Counter
import datetime as dt
import hashlib
import json

def dec(q):
    with localcontext() as ctx:
        ctx.prec=32
        return str(Dec(q.numerator)/Dec(q.denominator))

def check(m,n,alpha,ys,kind,physical):
    D=m*n
    ys=sorted(ys,reverse=True)
    assert len(ys)==D and sum(ys)==D and min(ys)>=0
    R=m*(m-1)//2;K=m*(m+1)//2;j=D-K+1
    mid=ys[R-1:j]
    N=D-m*m+2
    assert len(mid)==N and N>=2
    A=mid[-1];kap=mid[0]/A-1
    mu=sum(mid)/N
    powers={y:y**alpha for y in set(ys)}
    H=lambda y:powers[y]-1-alpha*(y-1)
    Hp=H(ys[0])
    if kap:
        xs=[(y-A)/(A*kap) for y in mid]
        theta=sum(xs)/N
        Zk=(1+kap)**alpha-1
        numer=sum(((1+kap*x)**alpha-1)/Zk for x in xs)
        loss=1-numer/sum(xs)
        assert 0<=loss<=1 and 0<theta<1
    else:
        theta=F(0);Zk=F(0);loss=F(1)
    assert A==mu/(1+kap*theta)
    body=N*(A**alpha*(1+theta*Zk*(1-loss))-1-alpha*(mu-1))
    assert body==sum(H(y) for y in mid) and body>=0
    Z=(Hp+body)/D;C=1+Z
    others=ys[1:R-1]+ys[j:]
    RE=sum(H(y) for y in others)
    QE=sum((y-1)**2 for y in others)
    M=sum(powers[y] for y in ys)/D
    assert M==C+RE/D and C>=1 and M>=C
    assert RE<=3*alpha*alpha*QE*(1+Hp)
    assert M/C<=1+3*alpha*alpha*QE
    v=max(F(1),max(others))
    assert RE<=F(alpha*(alpha-1),2)*QE*v**(alpha-2)
    omitted_loss_rejected=False
    if kap and loss>0:
        wrong=1+(Hp+N*(A**alpha*(1+theta*Zk)-1-alpha*(mu-1)))/D
        assert wrong>C
        omitted_loss_rejected=True
    omitted_mean_rejected=False
    if mu!=1:
        wrong=1+(Hp+N*(A**alpha*(1+theta*Zk*(1-loss))-1))/D
        assert wrong!=C and wrong-C==F(alpha*N,D)*(mu-1)
        omitted_mean_rejected=True
    return {'kind':kind,'m':m,'n':n,'D':D,'alpha':alpha,'N_actual':N,
      'physical_APPT_reason':physical,
      'actual_middle_mean_minus1_exact':str(mu-1),'actual_kappa_exact':str(kap),
      'actual_theta_exact':str(theta),'actual_chord_loss_decimal':dec(loss),
      'C_over_M_decimal':dec(C/M),
      'exact_centered_reconstruction':True,'polynomial_peak_comparison_exact':True,
      'actual_exception_kernel_bound_exact':True,
      'omitting_nonzero_chord_loss_rejected':omitted_loss_rejected,
      'omitting_nonzero_actual_mean_rejected':omitted_mean_rejected,
      'finite_optimum_used':False}

rows=[]
for m,alphas in [(4,[2,3,8,67]),(6,[2,5,36,217]),(8,[3,20,513])]:
    n=m*m;D=m*n
    for alpha in alphas:
        assert D%4==0
        ys=[F(m+1,m)]*(D//4)+[F(1)]*(D//2)+[F(m-1,m)]*(D//4)
        rows.append(check(m,n,alpha,ys,'three_level_actual_contraction',
          'rho=(I+[2/(m-1)]X)/Tr with0<=X<=I and levels0,1/2,1; Schmidt negative-sum witness proves all-global-unitary APPT'))
        ys=[F(3*D,D+2)]+[F(D,D+2)]*(D-1)
        rows.append(check(m,n,alpha,ys,'actual_exact_pure_spike',
          '(I+2vv*)/(D+2), pure PT least eigenvalue>=-1/2'))
        ys=[F(D,D-1)]*(D-1)+[F(0)]
        rows.append(check(m,n,alpha,ys,'actual_singular_hole',
          '(I-vv*)/(D-1), pure PT largest eigenvalue<=1'))
        k=D//2;kap=F(1,m-1)
        eta=2*(m-2)*kap**2/(2-(m-3)*kap)
        d=2-kap-eta
        z=1+kap*F(k,D)+d/D
        assert d>=0
        ys=[(3-eta)/z]+[(1+kap)/z]*(k-1)+[1/z]*(D-k)
        rows.append(check(m,n,alpha,ys,'actual_protected_projection_spike',
          'rho=(I+kappaP+dvv*)/(D+kappak+d),v inrangeP, d=2-kappa-eta; credited exact G26/V12 Schmidt SOS, actual integer rank'))
    rows.append(check(m,n,alphas[-1],[F(1)]*D,'actual_maximally_mixed','I/D is APPT under every global unitary'))

assert any(r['omitting_nonzero_chord_loss_rejected'] for r in rows)
assert any(r['omitting_nonzero_actual_mean_rejected'] for r in rows)
assert any(r['alpha']>r['D'] for r in rows)
assert any(r['kind']=='actual_singular_hole' for r in rows)
paper=Path(__file__).with_name('PAPER.md');source=Path(__file__)
out={'utc':dt.datetime.now(dt.timezone.utc).isoformat(),
 'scope':'Author finite actual-spectrum regressions only, not independent review, global rates or Lean',
 'paper_sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'arithmetic':'All ranks/spectra/mean/loss/kernel/reconstruction/inequalities use Fraction and integers; Decimal32 displays only',
 'finite_cases':len(rows),'rows':rows,'all_requested_assertions_passed':True,
 'not_proof_of_universal_theorems':True,'no_finite_optimum_assumed':True}
dest=source.with_name('AUTHOR_EXACT_CONTROLS.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':out['paper_sha256'],'source_sha256':out['source_sha256'],
 'finite_cases':len(rows),'all_requested_assertions_passed':True,'result_bytes':dest.stat().st_size},indent=2))
