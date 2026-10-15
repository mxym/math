"""Finite controls for the fixed-decoder testing reduction.

Complete logical equivalence is proved in the accompanying written note.
These enumerated formulas are controls, not a complexity-theorem substitute.
No SAT solver is used by this file.
"""
from itertools import combinations, product
from pathlib import Path
import json

HERE=Path(__file__).parent

def small_masks(n,k):
    return [sum(1<<i for i in A) for j in range(k+1)
            for A in combinations(range(n),j)]

def build(v,clauses):
    m=len(clauses)
    if v<1 or m<1 or any(not c or any(abs(l)<1 or abs(l)>v for l in c) for c in clauses):
        raise ValueError('Expected a nonempty CNF on v>=1 declared variables')
    L=v+m; N=1+3*v+m; n=N+2; r=0
    def literal(i,positive):
        return L+1+2*(i-1)+(0 if positive else 1)
    def bit(i):
        return 1<<i
    def B(U):
        A=[i for i in range(N) if (U>>i)&1]
        if not A:
            return bit(r)
        if len(A)==1:
            x=A[0]
            if x==r:
                return bit(1)
            if 1<=x<L:
                return bit(x+1)
            return bit(r)
        if len(A)!=2:
            raise ValueError('Message too large')
        i,j=A
        if i==r and 1<=j<=v:
            return bit(literal(j,True))|bit(literal(j,False))
        if i==r and v<j<=L:
            return sum({bit(literal(abs(l),l>0)) for l in clauses[j-v-1]})
        if any(set(A)=={literal(t,True),literal(t,False)} for t in range(1,v+1)):
            return 0
        if i!=r:
            return bit(r)
        return bit(1)
    coremask=(1<<N)-1; tags=(1<<N)|(1<<(N+1))
    C=[0,1<<N,1<<(N+1),tags]
    masks=small_masks(n,2)
    messages={(a,c&a) for a in masks for c in C}
    H={}
    for a,b in messages:
        if a&tags:
            H[(a,b)]=b
        else:
            H[(a,b)]=B(a)
        if H[(a,b)]&a!=b:
            raise ValueError('Constructed decoder is not normalized')
    return n,N,C,H,literal

def assignment_domains(v,clauses,N,literal):
    L=v+len(clauses)
    result=[]
    for assignment in product([False,True],repeat=v):
        sat=all(any(assignment[abs(l)-1] == (l>0) for l in clause) for clause in clauses)
        if sat:
            A=(1<<(L+1))-1
            A|=sum(1<<literal(i+1,b) for i,b in enumerate(assignment))
            result.append(A)
    return sorted(result)

def controls(v,clauses):
    n,N,C,H,literal=build(v,clauses)
    core_messages=[(a,h) for (a,b),h in H.items() if a<(1<<N)]
    actual=[]
    for A in range(1<<N):
        if not any(not(u&~A) and not(h&A) for u,h in core_messages):
            actual.append(A)
    expected=assignment_domains(v,clauses,N,literal)
    if actual!=expected:
        raise ValueError('All-core-sample enumeration disagrees with CNF truth table')
    # Independently verify the promised tag-only cover for every realizable
    # sample with at least one tag, including both tag labels and core subsets.
    checked_tags=0
    for tag_pattern in product([-1,0,1],repeat=2):
        if tag_pattern==(-1,-1):
            continue
        u=sum(1<<(N+i) for i,b in enumerate(tag_pattern) if b!=-1)
        lab=sum(1<<(N+i) for i,b in enumerate(tag_pattern) if b==1)
        h=H[(u,lab)]
        for A in range(1<<N):
            a=A|u
            if h&a!=lab:
                raise ValueError('Tag-only message fails a tagged sample')
            checked_tags+=1
    return {'variables':v,'clauses':clauses,'n':n,'core_coordinates':N,
            'concept_count':4,'actual_VC':2,'compression_bound':2,
            'messages':len(H),'all_core_samples_enumerated':1<<N,
            'all_tagged_realizable_samples_checked':checked_tags,
            'satisfying_assignments':len(expected),'failed_domains':actual,
            'bijection_verified':True,
            'every_failed_domain_has_size':2*v+len(clauses)+1 if actual else None,
            'scope':'Only this listed formula control; full equivalence and complexity proof are written, not inferred from the cases.'}

def long_failure(n):
    cycle=n-1
    f={i:(i+1)%cycle for i in range(cycle)}; f[n-1]=0
    failures=[]
    for A in range(1,(1<<n)-1):
        if all((A>>f[i])&1 for i in range(n) if (A>>i)&1):
            failures.append(A)
    if failures!=[(1<<(n-1))-1]:
        raise ValueError('Long hidden-failure example has an unexpected invariant domain')
    return {'n':n,'VC':1,'compression_bound':1,
            'smallest_failed_sample_size':n-1,
            'every_sample_up_to_size_passes':n-2,
            'all_complete_rows_pass':True,
            'failed_domain':failures[0]}

if __name__=='__main__':
    cases=[(1,[[1,1,1]]),(1,[[1,1,1],[-1,-1,-1]]),
           (2,[[1,2,2],[-1,2,2],[1,-2,-2]]),
           (2,[[1,2,2],[-1,2,2],[1,-2,-2],[-1,-2,-2]]),
           (3,[[1,2,3],[-1,2,-3]])]
    result={'formula_controls':[controls(v,c) for v,c in cases],
            'long_failure_controls':[long_failure(n) for n in range(3,13)],
            'scope':'Author-only finite controls of auxiliary fixed-decoder verification results. Not SC0 resolution or an independent mathematical review.'}
    (HERE/'FIXED_DECODER_COMPLEXITY_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
