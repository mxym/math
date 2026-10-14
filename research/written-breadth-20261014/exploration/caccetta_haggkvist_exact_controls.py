"""Exact whole-target shortcut controls; no CH solution or counterexample."""
from fractions import Fraction as F
from pathlib import Path
import json, itertools

def trim(p):
    while len(p)>1 and p[-1]==0: p.pop()
    return p
def add(p,q):
    r=[F(0)]*max(len(p),len(q))
    for i,x in enumerate(p): r[i]+=x
    for i,x in enumerate(q): r[i]+=x
    return trim(r)
def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]+=x*y
    return trim(r)
def scale(p,x): return trim([x*y for y in p])
def power(p,n):
    r=[F(1)]
    for _ in range(n): r=mul(r,p)
    return r
def rem(p,q):
    p=p.copy()
    while len(p)>=len(q):
        d=len(p)-len(q);v=p[-1]/q[-1]
        for i,x in enumerate(q): p[i+d]-=v*x
        trim(p)
    return p
def rat(x): return [x.numerator,x.denominator]
def matmul(a,b):
    n=len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def traces(a,k):
    n=len(a);p=[[int(i==j) for j in range(n)] for i in range(n)];r=[]
    for _ in range(k):
        p=matmul(p,a);r.append(sum(p[i][i] for i in range(n)))
    return r
def bfs(a,start):
    ds=[None]*len(a);ds[start]=0;q=[start]
    for v in q:
        for w,b in enumerate(a[v]):
            if b and ds[w] is None: ds[w]=ds[v]+1;q.append(w)
    return ds
def girth(a):
    best=len(a)+1
    for v in range(len(a)):
        d=bfs(a,v)
        for w in range(len(a)):
            if a[w][v] and d[w] is not None: best=min(best,d[w]+1)
    return best
def det_integer(a):
    a=[row[:] for row in a];n=len(a);sign=1;previous=1
    if n==0: return 1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None: return 0
        if pivot!=k: a[k],a[pivot]=a[pivot],a[k];sign=-sign
        v=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=v*a[i][j]-a[i][k]*a[k][j]
                assert numerator%previous==0
                a[i][j]=numerator//previous
            a[i][k]=0
        previous=v
    return sign*a[-1][-1]
def actual_record(a,r):
    n=len(a)
    assert all(all(v in (0,1) for v in row) for row in a)
    assert all(a[i][i]==0 for i in range(n))
    degrees=list(map(sum,a));assert set(degrees)=={r}
    assert all(all(v is not None for v in bfs(a,i)) for i in range(n))
    g=girth(a);assert g<= (n+r-1)//r
    tr=traces(a,g);assert tr[:g-1]==[0]*(g-1) and tr[g-1]>0
    return {'n':n,'r':r,'out_degrees':degrees,'strongly_connected':True,'directed_girth_BFS':g,
            'conjectured_length_bound':(n+r-1)//r,'independent_closed_walk_traces':tr,
            'adjacency':a,'is_CH_counterexample':False}

N=M=64;lo=F(39,100);hi=F(2,5)
f=lambda a:16*a**3+(1+2*a)**3/N**2-1
assert f(lo)<0<f(hi)
epsilon_upper=(1+2*hi)/N
tau_lower=1-4*hi**2
tau_upper=1-4*lo**2+(1+2*hi)**2/N
delta_squared_upper=tau_upper/(2*M)
assert tau_lower>0 and delta_squared_upper<F(3,50)**2
energy_upper=2+4*hi**2+2*(1+2*hi)**2/N
higher_trace_lower=1-2*(2*hi)**4-N*epsilon_upper**4-2*M*F(3,50)**4
assert energy_upper<3 and higher_trace_lower>0
a=[F(0),F(1)];epsilon=[F(1,64),F(1,32)]
tau=add(add([F(1)],scale(power(a,2),F(-4))),scale(power(epsilon,2),F(64)))
p4=add(add(add([F(1)],scale(power(a,4),F(-16))),scale(power(epsilon,4),F(64))),scale(power(tau,2),F(1,128)))
minimal=[F(-1365),F(2),F(4),F(21848)]
p4_reduced=rem(p4,minimal)
roots_mod11=[sum(int(c)*x**i for i,c in enumerate(minimal))%11 for x in range(11)]
assert 0 not in roots_mod11 and int(minimal[-1])%11!=0
assert len(p4_reduced)>1 and any(p4_reduced[1:])
spectral={'spectrum_size':195,'comparison_n':195,'comparison_r':65,
          'a_unique_positive_root_minimal_polynomial_increasing_coefficients':list(map(int,minimal)),
          'a_interval':[rat(lo),rat(hi)],'cubic_at_interval_ends':[rat(f(lo)),rat(f(hi))],
          'epsilon_definition':'(1+2a)/64','tau_definition':'1-4a^2+64epsilon^2',
          'delta_squared_definition':'tau/128',
          'spectrum':'1; a +/- i sqrt(3)a; 64 copies of -epsilon; 64 pairs +/- i delta',
          'exact_zero_power_sums':[1,2,3],
          'tau_bounds':[rat(tau_lower),rat(tau_upper)],
          'delta_squared_upper':rat(delta_squared_upper),
          'squared_spectral_energy_upper':rat(energy_upper),
          'strict_lower_bound_for_every_power_sum_j_ge4':rat(higher_trace_lower),
          'irreducible_cubic_mod11_root_values':roots_mod11,
          'fourth_power_sum_reduced_coefficients':[rat(x) for x in p4_reduced],
          'integer_realization_rejected':True,
          'rejection_reason':'The fourth power sum is irrational by irreducibility and nonconstant degree<=2 reduction. Scaling by65^4 cannot equal the integer trace(A^4).',
          'is_CH_counterexample':False}

layer=[[0]*16 for _ in range(16)]
AA=range(1,5);BB=range(5,8);CC=range(8,12);DD=range(12,16)
for i in AA:
    layer[i][1+(i%4)]=1
    for j in BB: layer[i][j]=1
for i in BB:
    for j in CC: layer[i][j]=1
for i in CC:
    for j in DD: layer[i][j]=1
for i in DD:
    for j in [0,1,2,3]: layer[i][j]=1
for j in AA: layer[0][j]=1
lr=actual_record(layer,4)
dist=bfs(layer,0)
lr['exact_distance_layers_from0']={d:dist.count(d) for d in sorted(set(dist))}
assert lr['directed_girth_BFS']==4 and lr['exact_distance_layers_from0']=={0:1,1:4,2:3,3:4,4:4}
lr['rejected_shortcut']='Every exact distance layer up to g-1 has size>=r, or every radius(g-1) ball has size>=1+r(g-1).'

coef=[[0]*14 for _ in range(14)]
for base in [0,7]:
    for i in range(7):
        for step in [1,2]: coef[base+i][base+(i+step)%7]=1
coef[0][1]=0;coef[0][8]=1;coef[7][8]=0;coef[7][1]=1
cr=actual_record(coef,2)
ts=traces(coef,14);coeff=[1]
for k in range(1,15):
    num=-sum(coeff[k-j]*ts[j-1] for j in range(1,k+1))
    assert num%k==0
    coeff.append(num//k)
direct_minor_sum=sum(det_integer([[coef[i][j] for j in S] for i in S])
                     for S in itertools.combinations(range(14),8))
assert coeff[8]==direct_minor_sum==35
cr.update({'traces1to14':ts,'det_I_minus_z_A_coefficients':coeff,
           'independent_order8_principal_minor_sum':direct_minor_sum,
           'all_order8_principal_minors_counted':3003,
           'rejected_shortcut':'Every nonconstant determinant coefficient is nonpositive, even after reduction to strong/out-regular actual graphs.'})
result={'scope':'Exact route controls for the complete all-n/all-r CH target; no full solution, no counterexample and no major-result credit.',
        'spectral_relaxation':spectral,'actual_distance_layer_control':lr,'actual_determinant_coefficient_control':cr}
out=Path(__file__).with_name('caccetta-haggkvist-exact-controls.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'path':str(out),'spectral_integer_realization_rejected':True,
                  'actual_controls':2,'order8_coefficient':35,'order8_principal_minors':3003,
                  'all_actual_controls_satisfy_CH':True}))
