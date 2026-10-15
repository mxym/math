"""Parse and validate every author result entry; never execute author code."""
from pathlib import Path
import hashlib, json, math
import mpmath as mp
ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'independent-review'
mp.mp.dps=180
def hh(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected={'README.md':'4b6d830d63ac40054c32d6e3180cae80ec32cc0badecaad05243a070809c3bd9','LITERATURE.md':'15f66fa0d56f66f65f870cac1fa3c5db5dd6e7eea5ff7757126751fc3872cdee','derive_coefficients.py':'ff3d517314245ab9e0868b06cbf4296e4f042b24c5470acb63941d53bb26af2d','check_expansion.py':'ca38c864018835c65774126883bdc7c0a304f2c9646240edea024a1f20574d1e','author_checks.json':'a3fd31b17bf5f5b6013e2a31ecb2002c7d6889ac64137d2ee8dfc8415f3c2a5c'}
manifest=[]
for f,sha in expected.items():
 p=ROOT/f; assert hh(p)==sha,(f,hh(p))
 (OUT/('AUTHOR_SNAPSHOT_'+f)).write_bytes(p.read_bytes())
 manifest.append(dict(path=f,sha256=hh(p),lines=len(p.read_text().splitlines()),reading='full sequential support read' if f!='author_checks.json' else 'entire JSON parsed; every row and manifest validated; not 705 raw lines read sequentially'))
r=json.loads((ROOT/'author_checks.json').read_text())
assert r['status']=='PASS_AUTHOR_FINITE_CONTROLS'
assert r['digits']==180 and r['mpmath']=='1.2.1'
assert r['new_Lean'] is False and r['whole_domain_certificate'] is False and r['external_human_review'] is False
for f,item in r['files'].items():
 p=ROOT/f
 assert hh(p)==item['sha256'] and len(p.read_text().splitlines())==item['lines']
assert len(r['files'])==4 and len(r['rows'])==48
assert r['false_fixed_z_second_order']['rejected'] is True
assert mp.mpf(r['false_fixed_z_second_order']['missing_at_a_5_over_4'])==4
rows=[]
for ix,row in enumerate(r['rows']):
 m=row['m']; n=row['n']; assert isinstance(m,int) and isinstance(n,int) and 3<=m<=n
 D=mp.mpf(m)*n; a=mp.mpf(row['a']); z=mp.mpf(row['z_continuous'])
 assert 1<z<3 and abs(a-(mp.mpf(n)-mp.mpf(m*m)/4)/m)<mp.mpf('1e-35')
 assert abs(mp.mpf(row['z_first_order_error_scaled_m2'])-(z-2-(28-16*a)/m)*m*m)<mp.mpf('1e-24')
 assert mp.isfinite(mp.mpf(row['second_order_value_error_scaled_m3']))
 assert abs(mp.mpf(row['second_order_value_error_scaled_m3']))<100000
 loss=mp.mpf(row['actual_integer_gap_scaled_m5']); assert 0<=loss<100
 ks=row['retained_floor_and_ceiling']; assert len(ks)==2 and all(isinstance(k,int) for k in ks)
 assert ks[1]-ks[0] in [0,1] and m*(m-1)//2<=ks[0]<=ks[1]<=m*n-m*(m+1)//2
 assert row['scope']=='Actual feasible candidates evaluated at continuous scalar optimum; not asserted to be full finite global optimum'
 # Re-evaluate retained actual candidates from the reported 45-digit scalar,
 # independently of the author's code, at 180 digits.
 t=mp.mpf(2)/(m-1); kap=2/(m-1+z); aa=2+kap; p=aa*z/(z+2); B=D*(1+kap)-kap*p-p*p
 pb=aa*aa/(4*B)
 actual=max((D+(2*kap+kap*kap)*k+2*(1+kap)*p+p*p)/(D+kap*k+p)**2 for k in ks)
 newloss=D*D*(pb-actual)*m**5
 assert abs(newloss-loss)<mp.mpf('1e-20')
 kq=((m-1)*n+1)//2; pg=(D+(2*t+t*t)*kq)/(D+t*kq)**2
 prediction=(5-4*a)/m+(16*a*a-44*a+37)/(m*m)
 newres=(D*D*(max(pg,actual)-pg)-max(0,prediction))*m**3
 assert abs(newres-mp.mpf(row['second_order_value_error_scaled_m3']))<mp.mpf('1e-20')
 rows.append(dict(index=ix,m=m,n=n,valid=True,reported_candidate_values_independently_recomputed=True))
failures=[]
for oldfile,logfile in [('INITIAL_DERIVE_COEFFICIENTS.py','INITIAL_EXPLORATORY_FAILURE.json'),('INITIAL_CHECK_EXPANSION.py','INITIAL_FINITE_GUARD_FAILURE.json')]:
 p=ROOT/oldfile; log=ROOT/logfile; data=json.loads(log.read_text())
 assert hh(p)==data['initial_script_sha256'] and data['raw_initial_script_retained'] is True
 for key in ['manuscript_math_changes','manuscript_mathematical_changes']:
  if key in data: assert data[key]==0
 (OUT/('AUTHOR_SNAPSHOT_'+oldfile)).write_bytes(p.read_bytes())
 (OUT/('AUTHOR_SNAPSHOT_'+logfile)).write_bytes(log.read_bytes())
 failures.append(dict(script=oldfile,script_sha256=hh(p),raw_record=logfile,raw_record_sha256=hh(log),cause=data['cause']))
o=dict(result='PASS_STRUCTURAL_AND_CANDIDATE_VALUE_VALIDATION',source_readings=manifest,all_raw_JSON_lines_sequentially_read=False,parsed_rows=len(rows),row_results=rows,source_manifest_checked_entries=len(r['files']),author_failures_preserved=failures,author_scripts_executed=False,Lean_executed=False,finite_values_are_actual_candidates_not_global_maxima=True)
(OUT/'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json').write_text(json.dumps(o,indent=2)+'\n')
print(json.dumps(dict(result=o['result'],rows=len(rows),support_line_total=sum(x['lines'] for x in manifest if x['path']!='author_checks.json'),author_failures=len(failures))))
