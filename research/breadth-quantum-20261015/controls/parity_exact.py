"""Exact integer partial traces of the parity-compressed determinant vector."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
import itertools, math, json, datetime
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')

def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def coefficient(d):
    perm=list(itertools.permutations(range(d)))
    return {(f,g):sign(f) for f in perm for g in perm if sign(f)==sign(g)}

def trace_norm(C,J,d):
    rem=[i for i in range(d) if i not in J]
    out=defaultdict(int)
    for (f,g),v in C.items():
        if all(f[j]==g[j] for j in J):
            out[(tuple(f[i] for i in rem),tuple(g[i] for i in rem))]+=v
    return sum(v*v for v in out.values())

records=[]
for d in [2,3,4,5,6]:
    C=coefficient(d);norm=sum(v*v for v in C.values());rows=[]
    for j in range(d+1):
        # Permuting resource slots preserves norms, so one representative
        # controls each size; for d<=4 verify EVERY subset independently.
        samples=list(itertools.combinations(range(d),j)) if d<=4 else [tuple(range(j))]
        vals=[trace_norm(C,J,d) for J in samples]
        expected=norm if j==0 else (norm//d if j==1 and d>=3 else (2 if j==1 else 0))
        assert all(x==expected for x in vals),(d,j,vals,expected)
        rows.append({'traced_slots':j,'subsets_directly_checked':len(samples),'squared_HS_norm':vals[0],'expected':expected})
    qhalf=sum(Fraction(-1,2)**j*math.comb(d,j)*r['squared_HS_norm'] for j,r in enumerate(rows))
    if d>=3:assert qhalf==Fraction(norm,2)
    rec={'d':d,'rank':2,'coefficient_HS2':norm,'trace_norms':rows,'Q_endpoint_exact':str(qhalf),'comparison_claim_Eq25':str(-Fraction(math.factorial(d)**2,4)) if d==3 else None}
    records.append(rec);print(json.dumps(rec),flush=True)

# For d=3, the old Eq. (22) right side is independently -9:
# only h=identity contributes, and det(I-(1/2)J_3)=-1/2.
assert records[1]['Q_endpoint_exact']=='9'
source_control={'d':3,'lambda':'1/2','physical_Werner_denominator':'15/2','actual_raw_rank2_expectation':'9','normalized_vector_physical_expectation':'4/3375','old_Eq22_rhs':'-9','old_Eq25_rhs':'-9','antisymmetric_original_vector_rank':6,'original_raw_expectation':'-3','normalization_checked':True}
(PUBLIC/'PARITY_EXACT_CONTROLS.json').write_text(json.dumps({'schema':'parity-compression-exact-controls-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records,'old_claim_control':source_control,'scope':'exact route control and a particular old displayed identity; neither a full NPT solution nor a priority claim'},indent=2)+'\n')
