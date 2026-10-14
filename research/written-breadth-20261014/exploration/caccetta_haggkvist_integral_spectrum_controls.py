"""Exact integral-spectrum relaxation controls; never actual CH witnesses."""
from fractions import Fraction
from pathlib import Path
import json
from datetime import datetime,timezone
def multiply(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def power(a,n):
    c=[1]
    for _ in range(n):c=multiply(c,a)
    return c
def mobius(n):
    sign=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;sign=-sign
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    if n>1:sign=-sign
    return sign
lower=Fraction(1)-2*Fraction(35,54)**2-Fraction(1,2025)-2*Fraction(2,15)**2
assert lower==Fraction(4511,36450)
assert lower*15**4>16
assert Fraction(15)>Fraction(9,8)**2
cases=[]
for s in [5,7,11,13,17,19]:
    assert s>=5 and s%2 and s%3
    b2=Fraction(29*s*s-5,6);c=Fraction(4*s*s+15*s+5,6)
    assert b2.denominator==c.denominator==1
    b2=int(b2);c=int(c);r=3*s;n=9*s
    polynomial=[-r,1]
    polynomial=multiply(polynomial,[s*s+b2,-2*s,1])
    polynomial=multiply(polynomial,power([1,1],5*s))
    polynomial=multiply(polynomial,[c,0,1])
    polynomial=[0]*(4*s-5)+polynomial
    assert len(polynomial)==n+1 and polynomial[-1]==1
    q=[2,2*s];u=[2,0];p=[n]
    for j in range(1,65):
        if j>=2:q.append(2*s*q[-1]-(s*s+b2)*q[-2]);u.append(-c*u[-2])
        p.append(r**j+q[j]+5*s*(-1)**j+u[j])
    assert p[1:4]==[0,0,0]
    assert all(lower* r**j<=p[j]<2*r**j for j in range(4,65))
    energy=Fraction(22*s*s+10*s,9*s*s)
    assert energy<=Fraction(8,3)<3
    coefficients=polynomial[::-1]
    for j in range(1,13):
        assert p[j]+sum(coefficients[i]*p[j-i] for i in range(1,j))+j*coefficients[j]==0
    primitive=[]
    for j in range(1,65):
        v=sum(mobius(d)*p[j//d] for d in range(1,j+1) if j%d==0)
        assert v%j==0
        primitive.append(v//j)
    assert primitive[:3]==[0,0,0] and min(primitive[3:])>0
    cases.append({"s":s,"formal_n":n,"formal_r":r,"b_squared":b2,"c":c,
                  "zero_multiplicity":4*s-5,"integer_characteristic_polynomial_ascending":polynomial,
                  "power_sums_1_through_12":p[1:13],"squared_normalized_energy":[energy.numerator,energy.denominator],
                  "primitive_walk_orbit_counts_1_through_64":primitive,
                  "actual_binary_realization_provided":False})
result={"schema":"inadmissible-integral-spectrum-controls-v1",
        "checked_utc":datetime.now(timezone.utc).isoformat().replace("+00:00","Z"),
        "scope":"Exact finite controls for the written all-odd-s>=5,3-not-dividing-s algebraic family. No actual binary graph or CH counterexample.",
        "uniform_lower_power_sum_normalized":[lower.numerator,lower.denominator],
        "all_j_proof_boundary":"For j>=4, triangle bounds give lower=4511/36450 and upper<2. Integer characteristic polynomial gives integer primitive exponents in its formal Euler product. For j>=8 subtracting proper-divisor powers costs at most 2*j*r^(j/2); lower*15^4>16 and multiplication by sqrt(15) preserves lower*r^(j/2)>2*j. Orders4..7 have only vanished proper-divisor traces.",
        "cases":cases,"new_major_results":0,"actual_CH_counterexamples":0}
out=Path(__file__).with_name("caccetta-haggkvist-integral-spectrum-controls.json")
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"cases":len(cases),"uniform_lower":str(lower),"first_case_powers":cases[0]["power_sums_1_through_12"],"actual_witnesses":0,"path":str(out)}))
