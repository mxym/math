"""Compare one diagnostic implementation across execution environments."""
from pathlib import Path
import json
import math

packet=Path(__file__).resolve().parent
names=['DIAGNOSTICS_STANDARD.json','DIAGNOSTICS_OPTIMIZED.json','DIAGNOSTICS_WSL.json']
records=[json.loads((packet/name).read_text()) for name in names]
fields=['window_cases','entropy_vs_moment_cases','uncalibrated_base_negative_controls']
errors=[]; numeric_differences=[]
def compare(a,b,path):
    if isinstance(a,dict):
        if a.keys()!=b.keys():
            errors.append(path+' keys')
        else:
            for k in a:
                compare(a[k],b[k],path+'/'+k)
    elif isinstance(a,list):
        if len(a)!=len(b):
            errors.append(path+' length')
        else:
            for i,(x,y) in enumerate(zip(a,b)):
                compare(x,y,path+'/'+str(i))
    elif type(a) in (int,float):
        if not math.isclose(a,b,rel_tol=1e-12,abs_tol=1e-10):
            errors.append(path+' numerical tolerance')
        if a!=b:
            numeric_differences.append({'path':path,'absolute_difference':abs(a-b)})
    elif a!=b:
        errors.append(path+' value')
for index in (1,2):
    for field in fields:
        compare(records[0][field],records[index][field],names[index]+'/'+field)
if any(r['status']!='PASS' or r['case_count']!=42 for r in records):
    errors.append('Execution status or case count')
result={'kind':'Environment comparison, one implementation',
        'cases_per_run':42,'records':names,
        'absolute_tolerance':1e-10,'relative_tolerance':1e-12,
        'bit_identical_across_all_environments':not numeric_differences,
        'different_numeric_fields':len(numeric_differences),
        'maximum_absolute_difference':max((x['absolute_difference'] for x in numeric_differences),default=0),
        'independent_implementations':1,'universal_proof_by_comparison':False,
        'errors':errors,'status':'PASS' if not errors else 'FAIL'}
(packet/'DIAGNOSTIC_COMPARISON.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if errors:
    raise SystemExit(1)
