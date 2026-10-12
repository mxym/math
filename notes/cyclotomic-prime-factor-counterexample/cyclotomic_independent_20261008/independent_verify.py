#!/usr/bin/env python3
"""Independent exact-integer verification; no external packages or candidate code.
Ascending coefficient arrays. Rebuild Phi_n from x^n-1, then compute F two ways.
"""
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ORIGINAL = OUT.parent / 'cyclotomic_prime_factor_20261008' / 'certificate.json'

def trim(a):
    a = list(a)
    while len(a)>1 and a[-1] == 0:
        a.pop()
    return a

def times(a,b):
    r = [0] * (len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[i+j] += x*y
    return trim(r)

def long_divide(a,b):
    assert b[-1] == 1
    a = trim(a)
    q = [0]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a)>=len(b):
        k = len(a)-len(b)
        c = a[-1]
        q[k] += c
        for j,x in enumerate(b):
            a[k+j] -= c*x
        a = trim(a)
    return trim(q),a

def x_n_minus_one(n):
    return [-1]+[0]*(n-1)+[1]

# Construct all Phi_n <= 30 using ONLY x^n-1=prod_{d|n}Phi_d.
phi={}
for n in range(1,31):
    q = x_n_minus_one(n)
    for d in range(1,n):
        if n%d == 0:
            q,r = long_divide(q,phi[d])
            assert r == [0]
    phi[n]=q
    p=[1]
    for d in range(1,n+1):
        if n%d == 0:
            p=times(p,phi[d])
    assert p == x_n_minus_one(n)

orders = [4,9,25,30]
base=[1]
for n in orders:
    base=times(base,phi[n])
f=[1]
for _ in range(6):
    f=times(f,base)
assert len(base)==37 and len(f)==217

# Separate computation from rational form, using generalized binomial theorem.
# A single factor (1-x^m)^6 has binomial coefficients (1,-6,15,-20,15,-6,1).
# The coefficients of (1-x^m)^(-6) are C(t+5,5), checked by integer recurrence.
from math import comb, isqrt
cut=216
series=[1]+[0]*cut
for m in [1,6,10,15]:
    nxt=[0]*(cut+1)
    for t in range(cut//m+1):
        v=comb(t+5,5)
        for j in range(cut-m*t+1):
            nxt[j+m*t] += v*series[j]
    series=nxt
for m in [4,9,25,30]:
    nxt=[0]*(cut+1)
    for t in range(7):
        v=(-1)**t*comb(6,t)
        if m*t<=cut:
            for j in range(cut-m*t+1):
                nxt[j+m*t] += v*series[j]
    series=nxt
assert series == f

# A third exact check: logarithmic-derivative recurrence.
# n*c_n = 6*sum_{j=1}^n A_j*c_(n-j), with A_j the signed divisor sum.
A=[0]+[sum(m for m in [1,6,10,15] if j%m==0)-sum(m for m in [4,9,25,30] if j%m==0) for j in range(1,217)]
for n in range(1,217):
    assert n*f[n] == 6*sum(A[j]*f[n-j] for j in range(1,n+1))

# Also verify polynomial identity after clearing the rational denominator.
num=den=[1]
for n in [4,9,25,30]:
    num=times(num,x_n_minus_one(n))
for n in [1,6,10,15]:
    den=times(den,x_n_minus_one(n))
assert times(base,den)==num

# The centered-q-integer certificate.
w=[f[0]]+[f[i]-f[i-1] for i in range(1,109)]
assert f==f[::-1] and f[0]==f[-1]==1
assert len(w)==109 and w[0]==1 and min(w[1:])==5
assert all(a>0 for a in f) and all(a>0 for a in w)
reconstructed=[0]*217
for i,weight in enumerate(w):
    for k in range(i,217-i):
        reconstructed[k]+=weight
assert reconstructed==f
assert sum(f)==30**6==729000000
assert max(f)==f[108]==11434392 and f.count(max(f))==1

# Independent direct divisibility checks for every prime whose Phi_p degree <=216.
# Reduce x^p=1, then eliminate x^(p-1) using 1+x+...+x^(p-1)=0.
primes=[p for p in range(2,218) if all(p%d for d in range(2,isqrt(p)+1))]
prime_remainders={}
for p in primes:
    residue=[0]*p
    for k,a in enumerate(f):
        residue[k%p]+=a
    rem=trim([residue[r]-residue[p-1] for r in range(p-1)])
    assert rem != [0]
    # A different reduction, polynomial long division, must agree.
    _,rem2=long_divide(f,[1]*p)
    assert rem==rem2
    prime_remainders[str(p)]=rem

# Compare with frozen original certificate only AFTER independently completing all
# computations above. The original script is never read, imported, or executed.
original_bytes=ORIGINAL.read_bytes()
original=json.loads(original_bytes)
expected='64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad'
assert hashlib.sha256(original_bytes).hexdigest()==expected
assert original['base_coefficients_ascending']==base
assert original['coefficients_ascending']==f
assert original['centered_q_integer_weights']==w
assert original['prime_order_remainders']==prime_remainders

certificate={
    'schema':'independent-integer-cyclotomic-check-v1',
    'checked_on_utc':'2026-10-08',
    'expression':'(Phi_4(q)*Phi_9(q)*Phi_25(q)*Phi_30(q))^6',
    'cyclotomic_generation':'Phi_n=(q^n-1)/product(Phi_d: d|n, d<n), exact monic division',
    'cyclotomic_coefficients_ascending':{str(n):phi[n] for n in orders},
    'base_coefficients_ascending':base,
    'recurrence_check':'For all 1<=n<=216, n*c_n=6*sum_{j=1}^n A_j*c_(n-j); A_j=sum(m in {1,6,10,15}, m|j)-sum(m in {4,9,25,30}, m|j)',
    'independent_second_method':'generalized binomial expansion of ((1-q^4)(1-q^9)(1-q^25)(1-q^30)/((1-q)(1-q^6)(1-q^10)(1-q^15)))^6',
    'coefficients_ascending':f,
    'centered_q_integer_identity':'F(q)=sum_{i=0}^{108} w_i q^i [217-2i]_q',
    'weights_ascending':w,
    'degree':216,
    'positive_coefficient_count':217,
    'positive_weight_count':109,
    'positive_adjacent_difference_count_before_peak':108,
    'minimum_adjacent_difference_before_peak':min(w[1:]),
    'minimum_centered_q_integer_weight':min(w),
    'peak_index':108,
    'peak_value':f[108],
    'coefficient_sum':sum(f),
    'prime_order_remainders':prime_remainders,
    'prime_remainder_count':len(primes),
    'original_certificate_sha256':expected,
    'original_all_coefficients_weights_and_prime_remainders_match':True,
    'assertions':'All passed in standard-library Python exact integers, by two separate coefficient algorithms and two separate prime-remainder algorithms.',
}
output=OUT/'independent_certificate.json'
output.write_text(json.dumps(certificate,ensure_ascii=False,indent=2)+'\n')
print('All independent assertions passed.')
print('Phi factors:',{n:phi[n] for n in orders})
print('B:',base)
print('degree:',len(f)-1,'positive coefficients:',len(f),'positive weights:',len(w))
print('adjacent differences:',len(w)-1,'minimum:',min(w[1:]),'peak:',f[108])
print('sum:',sum(f),'checked primes:',len(primes),'largest:',primes[-1])
print('original coefficient, weight, and remainder arrays match exactly')
print('independent_certificate_sha256:',hashlib.sha256(output.read_bytes()).hexdigest())
print('weights:')
for start in range(0,len(w),10):
    print(start, w[start:start+10])
