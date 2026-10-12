#!/usr/bin/env python3
"""Author exact verification of the rank-one CRT-completed cubic eight-step example.

Public derivative: strict integer metadata validation and extra schema controls.
The original verifier is preserved in original-verifiers/.

Reuses only exact arithmetic definitions from the separate F6 verifier, and
reconstructs every quotient state and every directed edge from the input.
No search generator is imported.
"""
import copy
import json
import math
from pathlib import Path
from check_cubic_certificate import (require, vec, add, mul, matrix, det,
                                     in_principal, norm_polynomial,
                                     exact_integer_metadata, metadata_negative_cases)


def verify(data):
    exact_integer_metadata(data)
    require(data['format'] == 'cubic_rank_one_f8_lift_certificate_v1', 'Wrong format')
    require(data['order'] == {'basis':['1','theta','theta^2'],'relation':'theta^3=2'}, 'Wrong order')
    generators = [vec(x) for x in data['generators']]
    require(generators == [(0,1,0),(1,1,0),(1,0,1),(-1,1,1)], 'Wrong generators')
    norms = [abs(det(matrix(a))) for a in generators]
    require(norms == [2,3,5,11] == data['generator_norms'], 'Wrong exact norms')
    for a in generators:
        require(det(matrix(a)) == norm_polynomial(a), 'Norm mismatch')
    gamma = (1,0,0)
    for a in generators:
        gamma = mul(gamma,a)
    require(gamma == vec(data['common_ideal_period_generator']) == (6,1,4), 'Wrong product generator')
    q = data['quotient_modulus']; row = vec(data['quotient_row'])
    require(q == 330 and row == (1,128,214), 'Wrong quotient map')
    require(pow(row[1],3,q) == 2 and row[1]**2 % q == row[2], 'Not a ring map')
    require(abs(det(matrix(gamma))) == q, 'Wrong period ideal index')
    phi = lambda x,m=q: sum(a*b for a,b in zip(row,x)) % m
    for a,p in zip(generators,norms):
        m = matrix(a)
        require(all(phi(tuple(m[i][j] for i in range(3)),p)==0 for j in range(3)), 'Wrong generator kernel')
    m = matrix(gamma)
    require(all(phi(tuple(m[i][j] for i in range(3)))==0 for j in range(3)), 'Wrong period kernel')
    allowed = [s for s in range(q) if math.gcd(s,q)==1]
    require(allowed == data['allowed_states'], 'Incomplete allowed state set')
    for s in range(q):
        require((s in allowed)==all(not in_principal((s,0,0),a) for a in generators), 'Independent membership mismatch')
    sections = {}
    for item in data['lift_sections']:
        s=item['state'];y=vec(item['point'])
        require(type(s) is int and s in allowed and s not in sections, 'Invalid/duplicate state')
        require(phi(y)==s and all(not in_principal(y,a) for a in generators), 'Invalid lift section')
        sections[s]=y
    require(set(sections)==set(allowed), 'Missing lift section')
    F={(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1),(0,1,1),(0,-1,-1)}
    steps=[vec(x) for x in data['steps']]
    require(len(steps)==8 and set(steps)==F, 'Wrong explicit eight-step set')
    adjacency={s:[] for s in allowed};edge_count=0
    for s in allowed:
        for f in steps:
            t=(s+phi(f))%q
            if t in sections:
                require(add(sections[s],f)==sections[t], 'Nonzero voltage in lift section')
                adjacency[s].append(t);edge_count+=1
    left=set(allowed);components=[]
    while left:
        start=min(left);seen={start};todo=[start]
        while todo:
            for t in adjacency[todo.pop()]:
                if t not in seen:
                    seen.add(t);todo.append(t)
        left-=seen;components.append(sorted(seen))
    require(sorted(components)==sorted(sorted(c) for c in data['components']), 'Wrong components')
    sizes=sorted(map(len,components))
    result={'allowed_count':len(allowed),'directed_edge_count':edge_count,'component_sizes':sizes,'maximum_component_size':max(sizes)}
    require(result==data['summary'], 'Wrong summary')
    return {'status':'accepted','arithmetic':'exact integer arithmetic','period_ideal_index':q,'common_scalar_period':q,**result}


def negative_tests(data):
    cases=[]
    d=copy.deepcopy(data);d['allowed_states'].pop();cases.append(d)
    d=copy.deepcopy(data);d['quotient_row'][1]=127;cases.append(d)
    d=copy.deepcopy(data);d['lift_sections'][0]['point']=[7,1,4];cases.append(d)
    d=copy.deepcopy(data);d['lift_sections'][0]['point']=[331,0,0];cases.append(d) # same state, wrong edge lift
    d=copy.deepcopy(data);d['steps'].append([0,1,-1]);cases.append(d)
    d=copy.deepcopy(data);d['components'][0].pop();cases.append(d)
    d=copy.deepcopy(data);d['generator_norms'][3]=13;cases.append(d)
    cases.extend(metadata_negative_cases(data))
    for i,d in enumerate(cases):
        try:
            verify(d)
        except (ValueError,KeyError,TypeError):
            continue
        raise ValueError('Negative test accepted: '+str(i))
    return len(cases)


if __name__=='__main__':
    p=Path(__file__).resolve().parent
    data=json.loads((p/'cubic_rank_one_f8_certificate.json').read_text())
    result=verify(data);result['negative_tests_rejected']=negative_tests(data)
    print(json.dumps(result,indent=2))
