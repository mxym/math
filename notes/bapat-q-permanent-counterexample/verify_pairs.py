#!/usr/bin/env python3
"""Independent exact verifier using every pair-deleted product.
Standard library only. Every Gaussian synthetic division checks its remainder.
No recurrence or Koszul implementation is imported.
"""
import csv, hashlib, json, math, pathlib, time

ROOT = pathlib.Path(__file__).resolve().parent
OUT = pathlib.Path(__file__).parent
Z = (0, 0)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def sub(x,y): return (x[0]-y[0],x[1]-y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def divexact(x,y):
    den=y[0]*y[0]+y[1]*y[1]
    re=x[0]*y[0]+x[1]*y[1]
    im=x[1]*y[0]-x[0]*y[1]
    assert den and re%den==0 and im%den==0
    return (re//den,im//den)
def multiply_linear(p,a,b):
    out=[Z]*(len(p)+1)
    for k,c in enumerate(p):
        out[k]=add(out[k],mul(c,a))
        out[k+1]=add(out[k+1],mul(c,b))
    return out
def divide_linear(p,a,b):
    if a==Z:
        assert p[0]==Z and b!=Z
        return [divexact(c,b) for c in p[1:]]
    out=[]; previous=Z
    for c in p[:-1]:
        previous=divexact(sub(c,mul(b,previous)),a)
        out.append(previous)
    assert p[-1]==mul(b,previous)
    return out
def norm_squared(p):
    degree=len(p)-1
    return sum(math.factorial(k)*math.factorial(degree-k)*(c[0]**2+c[1]**2) for k,c in enumerate(p))

start=time.monotonic()
raw=(ROOT/'counterexample_vectors_n200.csv').read_bytes()
with (ROOT/'counterexample_vectors_n200.csv').open(newline='') as stream:
    reader=csv.reader(stream); assert next(reader)==['a_real','a_imag','b_real','b_imag']
    rows=[tuple(map(int,row)) for row in reader]
vectors=[((r[0],r[1]),(r[2],r[3])) for r in rows]
n=len(vectors); assert n==200
assert all(a!=Z or b!=Z for a,b in vectors)
F=[(1,0)]
for a,b in vectors: F=multiply_linear(F,a,b)
S=[Z]*(n-1)
pair_count=0
for i,(a,b) in enumerate(vectors):
    first=divide_linear(F,a,b)
    for c,d in vectors[i+1:]:
        second=divide_linear(first,c,d)
        wedge=sub(mul(a,d),mul(b,c))
        S=[add(v,mul(wedge,u)) for v,u in zip(S,second)]
        pair_count+=1
per=norm_squared(F); snorm=norm_squared(S); N=n*(n-1)//2
margin=snorm-N*per
assert pair_count==N and per>0 and margin>0 and margin%2==0
assert 23*N*per < 1000*margin < 24*N*per
reference=json.loads((ROOT/'expected_values.json').read_text())
computed={'permanent':str(per),'S_norm_squared':str(snorm),'N_permanent':str(N*per),'negative_twice_derivative':str(margin)}
assert all(computed[k]==reference[k] for k in computed)
assert max(abs(z) for row in rows for z in row)<=20
epsilon_den=4*N*math.factorial(n)*n*1601**(n-1)
q_gap_den=8*N*(N-1)*math.factorial(n)*1601**n
report={'method':'Independent exact division for each unordered pair; no author S recursion or Koszul implementation imported',
        'csv_sha256':hashlib.sha256(raw).hexdigest(),'n':n,'pairs':pair_count,
        'all_four_reference_integers_match':True,'margin_positive':True,'margin_digits':len(str(margin)),
        'maximum_row_norm_squared':max(sum(z*z for z in row) for row in rows),
        'epsilon_denominator':str(epsilon_den),'q_gap_denominator':str(q_gap_den),
        'exact_values':computed,'elapsed_seconds':time.monotonic()-start}
(OUT/'verification_pairs_result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['n','pairs','all_four_reference_integers_match','margin_positive','margin_digits','maximum_row_norm_squared','elapsed_seconds']}))
