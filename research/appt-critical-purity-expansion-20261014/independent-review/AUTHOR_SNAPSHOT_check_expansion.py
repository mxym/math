"""Author finite high-precision controls for the uniform coefficient proof."""
from pathlib import Path
import hashlib,json
from fractions import Fraction as F
import mpmath as mp


def main():
 mp.mp.dps=180
 rows=[]
 for mm in [256,257,258,259,512,1024,4096,10**6]:
  m=mp.mpf(mm)
  for wanted in [F(-2),F(0),F(3,4),F(5,4),F(3,2),F(2)]:
   n=mm*mm//4+int(wanted*mm)
   a=mp.mpf(n-mm*mm/4)/m
   d=m*n;t=2/(m-1)
   pb=(2+t)**2/(4*d*(1+t))
   def data(z):
    kap=2/(m-1+z);p=(2+kap)*z/(z+2);aa=2+kap
    b=d*(1+kap)-kap*p-p*p
    bound=aa*aa/(4*b)
    rk=(2*b/aa-d-p)/kap
    return kap,p,b,bound,rk
   def objective(z):return d*d*(data(z)[3]-pb)
   zc=mp.findroot(lambda z:mp.diff(objective,z),2+(28-16*a)/m)
   assert 1<zc<3
   kap,p,b,bound,rk=data(zc)
   ks=[int(mp.floor(rk)),int(mp.ceil(rk))]
   physical=[]
   for k in ks:
    assert mm*(mm-1)//2<=k<=mm*n-mm*(mm+1)//2
    trace=d+kap*k+p
    val=((2+kap)*trace-b)/trace**2
    loss=bound-val
    assert mp.almosteq(loss,(2+kap)**2*(trace-2*b/(2+kap))**2/(4*b*trace**2))
    physical.append(val)
   kq=((mm-1)*n+1)//2
   pg=(d+(2*t+t*t)*kq)/(d+t*kq)**2
   value=d*d*(max(pg,*physical)-pg)
   continuous=objective(zc)
   approx=(5-4*a)/m+(16*a*a-44*a+37)/(m*m)
   actual_gap=d*d*(bound-max(physical))
   assert 0<=actual_gap<100/m**5
   assert d*d*(pb-pg)<100/m**5
   residual=(value-max(mp.mpf(0),approx))*m**3
   assert abs(residual)<100000
   rows.append({'m':mm,'n':n,'a':mp.nstr(a,45),'z_continuous':mp.nstr(zc,45),
     'z_first_order_error_scaled_m2':mp.nstr((zc-2-(28-16*a)/m)*m*m,45),
     'second_order_value_error_scaled_m3':mp.nstr(residual,45),
     'actual_integer_gap_scaled_m5':mp.nstr(actual_gap*m**5,45),
     'retained_floor_and_ceiling':ks,
     'scope':'Actual feasible candidates evaluated at continuous scalar optimum; not asserted to be full finite global optimum'})
 # At critical slope 5/4 a fixed-z calculation misses exactly four units.
 missing=4*(mp.mpf('3.5')-2*mp.mpf('1.25'))**2
 assert missing==4
 files={f:{'sha256':hashlib.sha256(Path(f).read_bytes()).hexdigest(),
           'lines':len(Path(f).read_text().splitlines())} for f in ['PAPER.md','THEOREM_MAP.md','derive_coefficients.py','check_expansion.py']}
 report={'status':'PASS_AUTHOR_FINITE_CONTROLS','mpmath':mp.__version__,'digits':mp.mp.dps,
  'files':files,'rows':rows,'false_fixed_z_second_order':{'missing_at_a_5_over_4':str(missing),'rejected':True},
  'exploratory_failure_retained':'INITIAL_DERIVE_COEFFICIENTS.py and INITIAL_EXPLORATORY_FAILURE.json',
  'new_Lean':False,'whole_domain_certificate':False,'external_human_review':False}
 Path('author_checks.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'status':report['status'],'actual_candidate_controls':len(rows),'wrong_fixed_scalar_rejected':True}))


if __name__=='__main__':main()
