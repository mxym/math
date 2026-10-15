"""Diagnose, without hiding, the first finite-family diagnostic failure."""
from pathlib import Path
import json,mpmath as mp
p=Path(__file__).resolve().parent
rows=[]
for dps in [100,1100]:
 with mp.workdps(dps):
  for c in [10,12]:
   b=mp.expm1(2*c)/(2*c)*mp.exp(-1+2*c/mp.expm1(2*c))
   h=mp.mpf(1)/(2*c)-1/mp.expm1(2*c)
   for factor in map(mp.mpf,['0.5','1','2']):
    for m in [40,80,160]:
     alpha=c*m;targetr=factor*(b-1)
     n=max(m,int(mp.nint(mp.mpf(3)**alpha/(targetr*m))))
     D=m*n;r=mp.mpf(3)**alpha/D;k=int(mp.floor(h*D))
     kappa=mp.mpf(2)/(m-1);z=1+kappa*mp.mpf(k)/D
     MB=(mp.mpf(k)/D*(1+kappa)**alpha+(1-mp.mpf(k)/D))/z**alpha
     MP=(mp.mpf(D)/(D+2))**alpha*(r+mp.mpf(D-1)/D)
     err=abs(max(MB,MP)/max(b,1+r)-1)
     rows.append({'dps':dps,'c':c,'factor':str(factor),'m':m,'D_digits':len(str(D)),
                  'err':mp.nstr(err,30),'chosen_branch':'bulk' if MB>=MP else 'pole'})
record={'failed_run':'control-runs/20261015T111610.260147Z',
        'actual_failure':'strictly decreasing finite-family absolute discrepancy asserted even when all losses round to zero at 100 decimal places',
        'source_math_changed':False,'rows':rows}
(p/'FIRST_CONTROL_FAILURE_DIAGNOSIS.json').write_text(json.dumps(record,indent=2)+'\n')
for row in rows:print(json.dumps(row))
