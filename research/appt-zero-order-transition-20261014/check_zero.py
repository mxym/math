"""Finite exact geometry and high-precision diagnostics, not an infinite proof."""
from __future__ import annotations
import argparse,hashlib,json
from decimal import Decimal as Z,getcontext
from fractions import Fraction as F
from pathlib import Path

getcontext().prec=400
getcontext().Emin=-999999999999999999
getcontext().Emax=999999999999999999
TOL=Z('1e-230')
def require(v,msg):
    if not v: raise RuntimeError(msg)
def z(v):
    return Z(v.numerator)/Z(v.denominator) if isinstance(v,F) else Z(v)
def close(a,b,msg): require(abs(a-b)<=TOL*max(Z(1),abs(a),abs(b)),msg)
def g(r,a,th):
    if a==0:return Z(0)
    if a==1:return th*r*r.ln()/(1+(r-1)*th)-(1+(r-1)*th).ln()
    return ((1+th*((a*r.ln()).exp()-1)).ln()-a*(1+(r-1)*th).ln())/(a-1)
def thstar(r,a):
    t=r-1; L=r.ln()
    if a==0:return (t-L)/(t*L)
    if a==1:return (r*L-t)/(t*t)
    Q=(a*L).exp()
    return (Q-1-a*t)/(t*(a-1)*(Q-1))
def bulk(r,D,a):
    point=Z(D)*thstar(r,a); k=int(point)
    ks=sorted({max(1,min(D-1,k)),max(1,min(D-1,k+1))})
    return max((g(r,a,Z(i)/D),i) for i in ks)
def interval_sum(a,b,delta,i,j,start,end):
    nh=max(0,min(i,end)-start+1)
    nl=max(0,min(j,end)-max(start,i+1)+1)
    nd=max(0,end-max(start,j+1)+1)
    return nh*a+nl*b+nd*delta

def geometry():
    records=[]; cuts=0; moments=0
    for m in [3,4,5,8,12]:
        R=m*(m-1)//2; K=m*(m+1)//2; q=F(m+1,m-1)
        for n in [2*m,2*m+1,3*m]:
            D=m*n
            for delta in [F(1,100*(m+1)),F(1,10000*(m+1))]:
                hs={i:delta*F(m,D)+(1-delta)*F(max(0,i-D+K)-min(i,R),i) for i in range(1,D+1)}
                require(all(hs[i]<0 for i in range(1,D-m)), 'shifted negative signs')
                require(all(hs[i]>0 for i in range(D-m,D+1)), 'shifted positive signs including oldzero')
                count=0
                for i in range(1,D-m):
                    for j in range(D-m,D+1):
                        s=D-j; w=hs[j]/(hs[j]-hs[i])
                        a=delta+(1-delta)*D*(w/F(i)+(1-w)/F(j))
                        b=delta+(1-delta)*D*(1-w)/F(j)
                        require(a>b>delta,'floor cut strict levels')
                        require(i*a+(j-i)*b+s*delta==D,'floor cut exact trace')
                        h=interval_sum(a,b,delta,i,j,D-K+1,D)-interval_sum(a,b,delta,i,j,1,R)
                        require(h==0,'floor cut exact maximalSchmidt boundary')
                        r=a/b; theta=F(i,j); mu=F(D-s*delta,j)
                        require(mu==b*(1+(r-1)*theta) and mu>=1,'actual support mean')
                        if i<R:
                            require(i*(a-b)==(m-s)*b+s*delta and r<=m+1,'early floor identity')
                        elif i<=D-K:
                            require(R*a==(K-s)*b+s*delta and r<=q,'middle floor identity')
                            if s:
                                require(b>=1/q and r<=q-F(1,2*R),'uniform smaller ratio')
                            else:
                                require(a==q/(1+(q-1)*F(i,D)) and b==1/(1+(q-1)*F(i,D)), 'unchanged original bulk cut')
                        else:
                            ell=D-i
                            require((ell-m)*a==(ell-s)*b+s*delta and r<=m+1,'late floor identity')
                        for p in [2,3]:
                            lhs=(i*a**p+(j-i)*b**p+s*delta**p)/D
                            scalar=(1+theta*(r**p-1))/(1+(r-1)*theta)**p
                            rhs=F(j,D)*mu**p*scalar+F(s,D)*delta**p
                            require(lhs==rhs and lhs>=F(j,D)*scalar,'trace and floor power terms retained')
                            moments+=1
                        cuts+=1; count+=1
                require(count==(m+1)*(D-m-1),'all finite shifted cuts')
                records.append({'m':m,'n':n,'delta':str(delta),'cut_vertices':count,'surviving_vertices':m+1})
    return {'cases':records,'exact_cut_vertices':cuts,'exact_power_identities':moments}

def crossing_and_expansion():
    rows=[]; wrong=[]
    for m in [3,4,5,8,12]:
        r=z(F(m+1,m-1)); t=r-1; L=r.ln(); th0=thstar(r,Z(0))
        C0=(t/L).ln()-1+L/t; C1=C0-th0*(1-th0)*L*L/2
        require(C0>0 and 0<th0<1,'positive smallorder scalar')
        for e in [3,6,12,20]:
            D=m*m*10**e; hole=(Z(D)/Z(D-1)).ln()
            lo=1/(2*C0*D); hi=2/(C0*D)
            require(bulk(r,D,lo)[0]<hole<bulk(r,D,hi)[0],'crossing bracket')
            for _ in range(280):
                mid=(lo+hi)/2
                if bulk(r,D,mid)[0]<hole:lo=mid
                else:hi=mid
            tau=(lo+hi)/2
            two=1/(C0*D)+(1/(2*C0)-C1/(C0**3))/Z(D)**2
            scaled=(tau-two)*Z(D)**3
            rows.append({'m':m,'D':str(D),'tau':str(tau),'two_term':str(two),'scaled_third_order_remainder':str(scaled)})
            for beta_scale in [Z(0),Z('1e-40'),Z('0.25'),Z('0.75'),Z(1),Z('1.25'),Z(2)]:
                beta=beta_scale/C0; alpha=beta/D
                model=max(hole,bulk(r,D,alpha)[0]); target=max(Z(1),beta*C0)
                # This checks the proved exact model's scalar uniform expansion, not all APPT states.
                require(abs(Z(D)*model-target)<Z('0.1'),'finite beta expansion needs investigation')
            if e==20:
                require(abs(scaled)<Z('1e10'),'large finite crossing remainder unexpectedly large')
        D=m*m*10**6; alpha=1/Z(D)**2
        require((Z(D)/Z(D-1)).ln()>bulk(r,D,alpha)[0],'wrong positive-order bulk-only extension')
        wrong.append({'m':m,'D':str(D),'alpha':str(alpha),'actual_onehole_beats_all_bulk':True})
    return rows,wrong

def deficit(groups,alpha,D):
    require(sum(count for count,_ in groups)==D,'compressed physical integer counts')
    if alpha==0:
        rank=sum(count for count,x in groups if x>0)
        return (Z(D)/Z(rank)).ln()
    if alpha==1:
        return sum(Z(count)*x*x.ln() for count,x in groups if x>0)/D
    M=sum(Z(count)*(alpha*x.ln()).exp() for count,x in groups if x>0)/D
    return M.ln()/(alpha-1)

def physical_controls():
    mixtures=[]; depths=[]; local=[]; no_unphysical_input=True
    for m in [3,4,5,8,12]:
        r=z(F(m+1,m-1)); t=r-1; L=r.ln(); th0=thstar(r,Z(0))
        C0=(t/L).ln()-1+L/t
        for e in [3,6]:
            D=m*m*10**e; hole=(Z(D)/Z(D-1)).ln(); k=int(Z(D)*th0)
            b=1/(1+t*Z(k)/D)
            for scale in [Z('0.25'),Z('0.75'),Z(1),Z('1.25')]:
                beta=scale/C0; alpha=beta/D
                require(0<alpha<=Z('0.5'),'actual smallorder control domain')
                optmodel=max(hole,bulk(r,D,alpha)[0])
                for weight in [F(0),F(1,1000),F(1,10),F(1,2),F(1)]:
                    vf=z(weight); base=(1-vf)*Z(D)/Z(D-1)
                    groups=[(k,base+vf*r*b),(D-k-1,base+vf*b),(1,vf*b)]
                    # Rational versions certify exact trace and positivity of actual APPT convex mixtures.
                    rf=F(m+1,m-1); bf=1/(1+(rf-1)*F(k,D)); basef=(1-weight)*F(D,D-1)
                    exact=[(k,basef+weight*rf*bf),(D-k-1,basef+weight*bf),(1,weight*bf)]
                    require(sum(c*x for c,x in exact)==D and all(x>=0 for _,x in exact),'actual mixture exact trace/PSD')
                    val=deficit(groups,alpha,D)
                    require(val<=optmodel+TOL,'convex physical family beats endpoint envelope')
                    mixtures.append({'m':m,'D':str(D),'beta_scale':str(scale),'weight':str(weight),'scaled_deficit':str(Z(D)*val)})
                for depth,label in [(Z(D),'ordinary-exponential'),(Z(D)**2,'super-exponential')]:
                    epsilon=(-depth).exp()
                    require(epsilon>0,'nonzero physical hole underflow')
                    a=Z(D)*epsilon/(D-1+epsilon); body=Z(D)/(D-1+epsilon)
                    val=deficit([(D-1,body),(1,a)],alpha,D)
                    w=(alpha*a.ln()).exp()
                    delta=min(Z(1)/48,Z(1)/(2*(m+1)),Z(1)/(4*r),1/(1+50*beta)**2)
                    require(a<=delta,'physical hole comparison domain')
                    # A super-exponential strict gap may be below 400-place subtraction.
                    # Preserve an unresolved direct comparison rather than calling it equality.
                    require(val<=hole+TOL,'direct hole comparison exceeds roundoff tolerance')
                    M=(Z(D-1)*(alpha*body.ln()).exp()+w)/D
                    Mh=(Z(D-1)/D)*(alpha*(Z(D)/Z(D-1)).ln()).exp()
                    lower=(w-25*beta*a)/D
                    require(lower>0 and M-Mh>=lower-TOL,'retained trace strictmoment lower bound')
                    direct_resolved=(hole-val)>TOL*max(Z(1),abs(hole),abs(val))
                    depths.append({'m':m,'D':str(D),'beta_scale':str(scale),'depth':label,
                                   'epsilon_nonzero':True,'log_epsilon':str(-depth),'w':str(w),
                                   'scaled_deficit':str(Z(D)*val),'one_minus_w':str(1-w),
                                   'direct_subtraction_resolved':direct_resolved})
                    local.append({'m':m,'D':str(D),'beta_scale':str(scale),'depth':label,
                                  'analytic_margin_positive':True,
                                  'direct_subtraction_resolved':direct_resolved,
                                  'direct_unresolved_does_not_mean_equality':not direct_resolved})
    return {'actual_APPT_convex_mixtures':mixtures,'actual_fullrank_hole_depths':depths,
            'strict_physical_hole_comparisons':local,'actual_partial_transpose_argument':'Analytic P^Gamma<=I and convex closure; finite compressed spectra, not sampled unitary certificate'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);args=ap.parse_args()
    exact=geometry();crossing,wrong=crossing_and_expansion();phys=physical_controls()
    data={'status':'PASS_FINITE_ORDINARY_DIAGNOSTICS','precision_decimal_digits':400,'implementations':1,
          'infinite_APPT_proof_certificate':False,'new_Lean_execution':False,
          'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'exact_floor_geometry':exact,'scalar_crossings':crossing,'wrong_bulk_only_controls':wrong,
          'physical_controls':phys}
    Path(args.out).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':data['status'],'finite_floor_cuts':exact['exact_cut_vertices'],
                      'exact_moment_identities':exact['exact_power_identities'],'scalar_crossings':len(crossing),
                      'actual_mixtures':len(phys['actual_APPT_convex_mixtures']),
                      'actual_hole_depth_cases':len(phys['actual_fullrank_hole_depths']),
                      'wrong_bulk_only_controls':len(wrong),'infinite_proof_certificate':False},indent=2))
if __name__=='__main__':main()
